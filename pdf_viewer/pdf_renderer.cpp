#include "pdf_renderer.h"
#include "utils.h"
#include <qdatetime.h>
#include <algorithm>

extern bool SHOULD_DRAW_UNRENDERED_PAGES;
extern unsigned int FAILED_RENDER_RETRY_MILIES;

// the height in pixels of the tiny preview of a page drawn while the page isn't rendered (see
// render_preview_if_missing); its width is at most 8 times that, whatever the page's aspect ratio
static const float PREVIEW_MIN_HEIGHT_PX = 64.0f;

extern bool LINEAR_TEXTURE_FILTERING;
extern int NUM_V_SLICES;
extern int NUM_H_SLICES;
extern bool TOUCH_MODE;
extern bool CASE_SENSITIVE_SEARCH;
extern bool SMARTCASE_SEARCH;
extern float GAMMA;
extern float DARK_MODE_CONTRAST;
extern float CUSTOM_BACKGROUND_COLOR[3];
extern float CUSTOM_TEXT_COLOR[3];
extern float CUSTOM_COLOR_CONTRAST;
extern int MAX_PENDING_REQUESTS;
extern unsigned int CACHE_INVALID_MILIES;

PdfRenderer::PdfRenderer(int num_threads, bool* should_quit_pointer, fz_context* context_to_clone) : context_to_clone(context_to_clone),
pixmaps_to_drop(num_threads),
pixmap_drop_mutex(num_threads),
thread_rendering_mutex(num_threads),
thread_contexts(num_threads),
should_quit_pointer(should_quit_pointer),
num_threads(num_threads)
{

    // this interval must be less than cache invalidation time
    garbage_collect_timer.setInterval(1000);
    garbage_collect_timer.start();

    for (int i = 0; i < num_threads; i++) {
        thread_busy_status.push_back(false);
    }
    QObject::connect(&garbage_collect_timer, &QTimer::timeout, [&]() {
        delete_old_pages();
        });
}

fz_context* PdfRenderer::init_context() {
    return fz_clone_context(context_to_clone);
}


void PdfRenderer::start_threads() {

    for (int i = 0; i < num_threads; i++) {
        worker_threads.push_back(std::thread([&, i]() {
            run(i);
            }));
    }
    search_thread = std::thread([&]() {
        run_search(num_threads);
        });
}

void PdfRenderer::join_threads()
{
    for (auto& worker : worker_threads) {
        worker.join();
    }
    search_thread.join();
}


void PdfRenderer::add_request(std::wstring document_path, int page, bool should_render_annotations, float zoom_level, float display_scale, int index, int num_h_slices, int num_v_slices) {
    if (document_path.size() > 0) {
        RenderRequest req;
        req.path = document_path;
        req.page = page;
        req.zoom_level = zoom_level;
        req.slice_index = index;
        req.num_h_slices = num_h_slices;
        req.num_v_slices = num_v_slices;
        req.display_scale = display_scale;
        req.should_render_annotations = should_render_annotations;

        pending_requests_mutex.lock();
        // if the zoom level has changed, there is no point in previous requests with a different zoom level
        for (int i = pending_render_requests.size() - 1; i >= 0; i--) {
            if (pending_render_requests[i].path == req.path && pending_render_requests[i].page == req.page && (pending_render_requests[i].zoom_level != zoom_level)) {
                pending_render_requests.erase(pending_render_requests.begin() + i);
            }
        }
        bool should_add = true;
        for (size_t i = 0; i < pending_render_requests.size(); i++) {
            if (pending_render_requests[i] == req) {
                should_add = false;
            }
        }
        if (should_add) {
            pending_render_requests.push_back(req);
        }
        if (pending_render_requests.size() > (size_t) MAX_PENDING_REQUESTS) {
            pending_render_requests.erase(pending_render_requests.begin());
        }
        pending_requests_mutex.unlock();
    }
    else {
        std::wcout << "Error: could not find documnet" << std::endl;
    }
}
void PdfRenderer::add_request(std::wstring document_path,
    int page,
    std::wstring term,
    bool is_regex,
    std::vector<SearchResult>* out,
    float* percent_done,
    bool* is_searching,
    std::mutex* mut,
    std::optional<std::pair<int, int>> range) {

    if (document_path.size() > 0) {

        SearchRequest req;
        req.path = document_path;
        req.start_page = page;
        req.search_term = term;
        req.search_results_mutex = mut;
        req.search_results = out;
        req.percent_done = percent_done;
        req.is_searching = is_searching;
        req.range = range;
        req.is_regex = is_regex;

        search_request_mutex.lock();
        pending_search_request = req;
        search_request_mutex.unlock();
    }
    else {
        std::wcout << "Error: could not find document" << std::endl;
    }
}

//should only be called from the main thread

GLuint PdfRenderer::find_rendered_page(std::wstring path, int page, bool should_render_annotations, int index, int num_h_slices, int num_v_slices, float zoom_level, float display_scale, int* page_width, int* page_height) {
    if (path.size() > 0) {
        RenderRequest req;
        req.path = path;
        req.page = page;
        req.zoom_level = zoom_level;
        req.slice_index = index;
        req.num_h_slices = num_h_slices;
        req.num_v_slices = num_v_slices;
        req.display_scale = display_scale;
        req.should_render_annotations = should_render_annotations;
        cached_response_mutex.lock();
        GLuint result = 0;
        for (auto& cached_resp : cached_responses) {
            if (cached_resp.pending || cached_resp.failed) continue;

            if ((cached_resp.request == req) && (cached_resp.invalid == false)) {
                cached_resp.last_access_time = QDateTime::currentMSecsSinceEpoch();

                if (page_width) *page_width = cached_resp.width;
                if (page_height) *page_height = cached_resp.height;

                // We can only use OpenGL in the main thread, so we can not upload the rendered
                // pixmap into a texture in the worker thread, so whenever we get a rendered page
                // in the main thread, we initialize its OpenGL texture if it is not initialized already
                if (cached_resp.texture != 0) {
                    result = cached_resp.texture;
                }
                else {
                    glGenTextures(1, &result);
                    glBindTexture(GL_TEXTURE_2D, result);

                    if (LINEAR_TEXTURE_FILTERING) {
                        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
                        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
                    }
                    else {
                        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
                        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
                    }

#ifdef GL_CLAMP
                    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP);
                    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP);
#else
                    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
                    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
#endif


                    // OpenGL usually expects powers of two textures and since our pixmaps dimensions are
                    // often not powers of two, we set the unpack alignment to 1 (no alignment) 

                    glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
                    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, cached_resp.pixmap->w, cached_resp.pixmap->h, 0, GL_RGB, GL_UNSIGNED_BYTE, cached_resp.pixmap->samples);
                    glPixelStorei(GL_UNPACK_ALIGNMENT, 4);

                    // don't need the pixmap anymore
                    pixmap_drop_mutex[cached_resp.thread].lock();
                    pixmaps_to_drop[cached_resp.thread].push_back(cached_resp.pixmap);
                    cached_resp.texture = result;
                    pixmap_drop_mutex[cached_resp.thread].unlock();

                }
                break;
            }
        }
        cached_response_mutex.unlock();
        if (result == 0) {
            // A failed page isn't drawn and the worker treats it as already rendered, so without
            // this it would only be rendered again once its entry is evicted (which needs cache
            // pressure, so it may never happen). Failures can be transient, so the failed entry is
            // dropped a while after it failed and the request below renders the page again.
            cached_response_mutex.lock();
            unsigned int now_ms = QDateTime::currentMSecsSinceEpoch();
            for (int i = static_cast<int>(cached_responses.size()) - 1; i >= 0; i--) {
                const RenderResponse& resp = cached_responses[i];
                if (resp.failed && (resp.request == req) && ((now_ms - resp.last_access_time) > FAILED_RENDER_RETRY_MILIES)) {
                    cached_responses.erase(cached_responses.begin() + i);
                }
            }
            cached_response_mutex.unlock();
            if (TOUCH_MODE) {
                if (!no_rerender) {
                    add_request(path, page, should_render_annotations, zoom_level, display_scale, index, num_h_slices, num_v_slices);
                }
            }
            else {
                add_request(path, page, should_render_annotations, zoom_level, display_scale, index, num_h_slices, num_v_slices);
            }
            return try_closest_rendered_page(
                path,
                page,
                should_render_annotations,
                index,
                num_h_slices,
                num_v_slices,
                zoom_level,
                display_scale,
                page_width,
                page_height
            );
        }
        return result;
    }
    return 0;
}

GLuint PdfRenderer::try_closest_rendered_page(std::wstring doc_path, int page, bool should_render_annotations, int index, int num_h_slices, int num_v_slices, float zoom_level, float display_scale, int* page_width, int* page_height) {
    /*
    If the requested page is not available, we try to find the rendered page with the closest
    possible zoom level to our request and return that instead. A tiny preview of the whole page
    (see render_preview_if_missing) is only used when there is no other render at all: it shows
    the page's content in place of white, but any real render is better than it.
    */
    cached_response_mutex.lock();

    float min_diff = 10000.0f;
    float preview_min_diff = 10000.0f;
    GLuint best_texture = 0;
    GLuint preview_texture = 0;
    RenderResponse* best_response = nullptr;
    RenderResponse* preview_response = nullptr;

    for (auto& cached_resp : cached_responses) {
        if (cached_resp.pending || cached_resp.failed) continue;
        // previews aren't uploaded yet when they are first drawn (nobody ever requests their zoom
        // level, so find_rendered_page never uploads them): they are uploaded here, where their
        // texture is first needed
        bool not_uploaded_yet = cached_resp.preview && (cached_resp.texture == 0) && (cached_resp.pixmap != nullptr);
        if ((cached_resp.request.slice_index == index) &&
            (cached_resp.request.num_h_slices == num_h_slices) &&
            (cached_resp.request.num_v_slices == num_v_slices) &&
            (cached_resp.request.path == doc_path) &&
            (cached_resp.request.display_scale == display_scale) &&
            (cached_resp.request.should_render_annotations == should_render_annotations) &&
            (cached_resp.request.page == page) &&
            ((cached_resp.texture != 0) || not_uploaded_yet)) {
            float diff = cached_resp.request.zoom_level - zoom_level;
            if (cached_resp.preview) {
                if (diff <= preview_min_diff) {
                    preview_min_diff = diff;
                    preview_texture = cached_resp.texture;
                    preview_response = &cached_resp;
                }
            }
            else {
                if (diff <= min_diff) {
                    min_diff = diff;
                    best_texture = cached_resp.texture;
                    best_response = &cached_resp;
                }
            }
        }
    }
    if (!best_response && preview_response) {
        best_texture = preview_texture;
        best_response = preview_response;
    }
    if (best_response) {
        // the texture is going to be drawn until the requested one is rendered, so it counts as
        // used and delete_old_pages won't delete it from under us
        best_response->last_access_time = QDateTime::currentMSecsSinceEpoch();

        if (best_response->texture == 0) {
            glGenTextures(1, &best_texture);
            glBindTexture(GL_TEXTURE_2D, best_texture);

            if (LINEAR_TEXTURE_FILTERING) {
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
            }
            else {
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
            }

#ifdef GL_CLAMP
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP);
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP);
#else
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
#endif

            glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
            glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, best_response->pixmap->w, best_response->pixmap->h, 0, GL_RGB, GL_UNSIGNED_BYTE, best_response->pixmap->samples);
            glPixelStorei(GL_UNPACK_ALIGNMENT, 4);

            // don't need the pixmap anymore
            pixmap_drop_mutex[best_response->thread].lock();
            pixmaps_to_drop[best_response->thread].push_back(best_response->pixmap);
            best_response->texture = best_texture;
            pixmap_drop_mutex[best_response->thread].unlock();
        }

        if (page_width) *page_width = static_cast<int>(best_response->width * zoom_level / best_response->request.zoom_level);
        if (page_height) *page_height = static_cast<int>(best_response->height * zoom_level / best_response->request.zoom_level);
    }
    cached_response_mutex.unlock();
    return best_texture;
}

// Renders a tiny preview of req's whole page into the cache, unless one is there already or is
// being made. While a page isn't rendered (yet, or at all, when its render keeps failing), the
// preview is drawn in its place, stretched: it shows the page's actual content instead of white.
void PdfRenderer::render_preview_if_missing(int thread_index, fz_context* mupdf_context, fz_document* doc, const RenderRequest& req) {
    if (!SHOULD_DRAW_UNRENDERED_PAGES) return;
    if (doc == nullptr) return;

    fz_page* page = nullptr;
    float width = 0, height = 0;
    fz_var(page);
    fz_try(mupdf_context) {
        page = fz_load_page(mupdf_context, doc, req.page);
        fz_rect rect = fz_bound_page(mupdf_context, page);
        width = rect.x1 - rect.x0;
        height = rect.y1 - rect.y0;
    }
    fz_always(mupdf_context) {
        fz_drop_page(mupdf_context, page);
    }
    fz_catch(mupdf_context) {
        return;
    }
    if ((width <= 0) || (height <= 0)) return;

    RenderRequest preview_req = req;
    preview_req.slice_index = -1;
    preview_req.num_h_slices = 1;
    preview_req.num_v_slices = 1;
    preview_req.zoom_level = std::min(PREVIEW_MIN_HEIGHT_PX / (height * req.display_scale),
        8.0f * PREVIEW_MIN_HEIGHT_PX / (width * req.display_scale));

    // the entry is reserved before rendering, so that concurrent requests of the same page see it
    // as already being made and don't render the preview twice
    cached_response_mutex.lock();
    bool exists = false;
    for (const auto& cached : cached_responses) {
        if ((cached.request == preview_req) && (cached.invalid == false)) exists = true;
    }
    if (!exists) {
        RenderResponse resp;
        resp.thread = thread_index;
        resp.request = preview_req;
        resp.last_access_time = QDateTime::currentMSecsSinceEpoch();
        resp.preview = true;
        cached_responses.push_back(resp);
    }
    cached_response_mutex.unlock();
    if (exists) return;

    fz_pixmap* preview = nullptr;
    fz_page* preview_page = nullptr;
    fz_var(preview);
    fz_var(preview_page);
    fz_try(mupdf_context) {
        fz_matrix transform_matrix = fz_pre_scale(fz_identity, preview_req.zoom_level * preview_req.display_scale, preview_req.zoom_level * preview_req.display_scale);
        if (preview_req.should_render_annotations) {
            preview = fz_new_pixmap_from_page_number(mupdf_context, doc, preview_req.page, transform_matrix, fz_device_rgb(mupdf_context), 0);
        }
        else {
            preview_page = fz_load_page(mupdf_context, doc, preview_req.page);
            preview = fz_new_pixmap_from_page_contents(mupdf_context, preview_page, transform_matrix, fz_device_rgb(mupdf_context), 0);
        }
        if (preview && (GAMMA != 1.0f)) {
            fz_gamma_pixmap(mupdf_context, preview, GAMMA);
        }
    }
    fz_always(mupdf_context) {
        fz_drop_page(mupdf_context, preview_page);
    }
    fz_catch(mupdf_context) {
        preview = nullptr;
    }

    cached_response_mutex.lock();
    int index = -1;
    bool invalid = false;
    for (int i = 0; i < static_cast<int>(cached_responses.size()); i++) {
        RenderResponse& resp = cached_responses[i];
        if ((resp.thread == thread_index) && (resp.request == preview_req) && resp.pending) {
            index = i;
            invalid = resp.invalid;
        }
    }
    bool stored = false;
    if ((index >= 0) && preview && !invalid) {
        RenderResponse& resp = cached_responses[index];
        resp.pixmap = preview;
        resp.width = preview->w;
        resp.height = preview->h;
        resp.last_access_time = QDateTime::currentMSecsSinceEpoch();
        resp.pending = false;
        stored = true;
        preview = nullptr;
        index = -1;
    }
    if (index >= 0) {
        // the preview couldn't be rendered (it is tried again with the next request of the page),
        // or the reservation was invalidated while rendering (e.g. the document changed)
        cached_responses.erase(cached_responses.begin() + index);
    }
    cached_response_mutex.unlock();
    if (preview) {
        // the reservation was deleted while rendering (e.g. the document was closed)
        fz_drop_pixmap(mupdf_context, preview);
    }
    if (stored) {
        emit render_advance();
    }
}

void PdfRenderer::delete_old_pages(bool force_all, bool invalidate_all) {
    /*
    Deletes old cached pages. This function should only be called from the main thread.
    OpenGL textures are released immediately but pixmaps should be freed from the thread
    that created them, so we add old pixmaps to pixmaps_to_delete and delete them later from the worker thread
    */

    if (no_rerender) {
        // don't release while resizing, can cause a blank screen
        return;
    }

    cached_response_mutex.lock();
    std::vector<int> indices_to_delete;
    unsigned int now = QDateTime::currentMSecsSinceEpoch();
    std::vector<int> cached_response_times;

    for (size_t i = 0; i < cached_responses.size(); i++) {
        // tiny previews of pages (see render_preview_if_missing) don't push the deletion threshold:
        // they hold a handful of kilobytes, and there is one per page that was drawn at all (they
        // are still deleted when they get older than the threshold)
        if (!cached_responses[i].preview) {
            cached_response_times.push_back(now - cached_responses[i].last_access_time);
        }
    }

    int N = num_cached_pages * NUM_V_SLICES * NUM_H_SLICES;

    if (invalidate_all) {
        for (size_t i = 0; i < cached_responses.size(); i++) {
            cached_responses[i].invalid = true;
        }
        are_documents_invalidated = true;
    }

    if (force_all) {
        for (size_t i = 0; i < cached_responses.size(); i++) {
            indices_to_delete.push_back(i);
        }
        are_documents_invalidated = true;
    }
    else if (cached_response_times.size() > (size_t) N) {
        // we never delete N most recent pages
        // todo: make this configurable
        std::nth_element(cached_response_times.begin(), cached_response_times.begin() + N - 1, cached_response_times.end());


        unsigned int time_threshold = now - cached_response_times[N - 1];

        for (size_t i = 0; i < cached_responses.size(); i++) {
            if ((cached_responses[i].last_access_time < time_threshold)
                && ((now - cached_responses[i].last_access_time) > CACHE_INVALID_MILIES)) {
                indices_to_delete.push_back(i);
            }
        }
    }

    // We erase from back to front so that erasing one element does not change
    // the index of other elements
    for (int j = indices_to_delete.size() - 1; j >= 0; j--) {
        int index_to_delete = indices_to_delete[j];
        RenderResponse resp = cached_responses[index_to_delete];

        pixmap_drop_mutex[resp.thread].lock();
        if (resp.texture == 0) {
            pixmaps_to_drop[resp.thread].push_back(resp.pixmap);
        }
        pixmap_drop_mutex[resp.thread].unlock();

        if (resp.texture != 0) {
            glDeleteTextures(1, &resp.texture);
        }

        cached_responses.erase(cached_responses.begin() + index_to_delete);
    }
    cached_response_mutex.unlock();
}

void PdfRenderer::run_search(int thread_index)
{
    fz_context* mupdf_context = init_context();

    while (!(*should_quit_pointer)) {
        if (pending_search_request.has_value()) {

            search_request_mutex.lock();
            SearchRequest req = pending_search_request.value();
            pending_search_request = {};
            search_request_mutex.unlock();

            SearchCaseSensitivity search_case_sensitivity = SearchCaseSensitivity::CaseInsensitive;
            if (CASE_SENSITIVE_SEARCH) search_case_sensitivity = SearchCaseSensitivity::CaseSensitive;
            if (SMARTCASE_SEARCH) search_case_sensitivity = SearchCaseSensitivity::SmartCase;

            search_is_busy = true;
            searching_mutex.lock();
            fz_document* doc = get_document_with_path(thread_index, mupdf_context, req.path);

            int num_pages_in_document = fz_count_pages(mupdf_context, doc);

            int page_begin = 0;
            int page_end = num_pages_in_document - 1;

            if (req.range) {
                page_begin = req.range.value().first - 1;
                page_end = req.range.value().second - 1;
            }
            // make sure page range is valid {
            if (page_begin < 0) page_begin = 0;
            if (page_begin > num_pages_in_document - 1) page_begin = num_pages_in_document - 1;
            if (page_end < 0) page_end = 0;
            if (page_end > num_pages_in_document - 1) page_end = num_pages_in_document - 1;
            //}

            int num_pages = page_end - page_begin + 1;

            req.search_results_mutex->lock();
            req.search_results->clear();
            *req.is_searching = true;
            req.search_results_mutex->unlock();

            if (req.start_page > page_end || req.start_page < page_begin) {
                req.start_page = page_begin;
            }

            int num_handled_pages = 0;
            int i = req.start_page;
            while (num_handled_pages < num_pages && (!pending_search_request.has_value()) && (!(*should_quit_pointer))) {
                num_handled_pages++;

                fz_page* page = fz_load_page(mupdf_context, doc, i);

                fz_stext_page* stext_page = fz_new_stext_page_from_page_number(mupdf_context, doc, i, nullptr);

                std::vector<fz_stext_char*> flat_chars;
                get_flat_chars_from_stext_page(stext_page, flat_chars, false);
                std::wstring page_text;
                std::vector<int> page_begin_indices;
                flat_char_prism2(flat_chars, i, page_text, page_begin_indices);
                req.search_results_mutex->lock();

                std::vector<SearchResult> page_results;
                if (req.is_regex == false) {
                    page_results = search_text_with_index(page_text, page_begin_indices, req.search_term, search_case_sensitivity, 0, 0, 0);
                }
                else {
                    page_results = search_regex_with_index(page_text, page_begin_indices, req.search_term, search_case_sensitivity, 0, 0, 0);
                }

                for (auto& pr : page_results) {
                    pr.page = i;
                }

                req.search_results->insert(req.search_results->end(), page_results.begin(), page_results.end());
                req.search_results_mutex->unlock();

                if (num_handled_pages % 16 == 0) {
                    *req.percent_done = (float)num_handled_pages / num_pages;
                    //*invalidate_pointer = true;
                    emit search_advance();
                }

                fz_drop_stext_page(mupdf_context, stext_page);


                i++;
                if (i > page_end) {
                    i = page_begin;
                }
            }
            searching_mutex.unlock();
            req.search_results_mutex->lock();
            *req.is_searching = false;
            //*invalidate_pointer = true;
            //if (on_search_invalidate) {
            //	on_search_invalidate();
            //}
            emit search_advance();
            req.search_results_mutex->unlock();
        }
        else {
            search_is_busy = false;
            sleep_ms(100);
        }
    }
}

PdfRenderer::~PdfRenderer() {
}

fz_document* PdfRenderer::get_document_with_path(int thread_index, fz_context* mupdf_context, std::wstring path) {

    std::pair<int, std::wstring> document_id = std::make_pair(thread_index, path);

    {
        std::lock_guard<std::mutex> lock(opened_documents_mutex);
        if (opened_documents.find(document_id) != opened_documents.end()) {
            return opened_documents.at(document_id);
        }
    }

    fz_document* ret_val = nullptr;
    fz_try(mupdf_context) {
        ret_val = open_document_with_file_name(mupdf_context, path);

        if (fz_needs_password(mupdf_context, ret_val)) {
            if (document_passwords.find(path) != document_passwords.end()) {
                fz_authenticate_password(mupdf_context, ret_val, document_passwords[path].c_str());
            }
        }

        {

            std::lock_guard<std::mutex> lock(opened_documents_mutex);
            opened_documents[make_pair(thread_index, path)] = ret_val;
        }
    }
    fz_catch(mupdf_context) {
        std::wcout << "Error: could not open document" << std::endl;
    }

    return ret_val;
}

void PdfRenderer::delete_old_pixmaps(int thread_index, fz_context* mupdf_context) {
    // this function should only be called from the worker thread
    pixmap_drop_mutex[thread_index].lock();
    for (size_t i = 0; i < pixmaps_to_drop[thread_index].size(); i++) {
        fz_try(mupdf_context) {
            fz_drop_pixmap(mupdf_context, pixmaps_to_drop[thread_index][i]);
        }
        fz_catch(mupdf_context) {
            std::wcout << "Error: could not drop pixmap" << std::endl;
        }
    }
    pixmaps_to_drop[thread_index].clear();
    pixmap_drop_mutex[thread_index].unlock();
}
void PdfRenderer::clear_cache() {
    delete_old_pages(false, true);
}

void PdfRenderer::run(int thread_index) {
    fz_context* mupdf_context = init_context();
    thread_contexts[thread_index] = mupdf_context;

    while (!(*should_quit_pointer)) {
        pending_requests_mutex.lock();

        while (pending_render_requests.size() == 0) {
            pending_requests_mutex.unlock();
            cached_response_mutex.lock();
            for (int i = 0; i < cached_responses.size(); i++) {
                // failed entries are excluded: they are invalidated here otherwise, and since the
                // failure triggers a repaint (see the render_advance in the failure handling), they
                // would be rendered again every frame instead of retried at a bounded rate
                // (see find_rendered_page)
                if ((cached_responses[i].thread == thread_index) && (cached_responses[i].texture == 0) &&
                    (cached_responses[i].pixmap == nullptr) && (cached_responses[i].failed == false)) {
                    cached_responses[i].invalid = true;
                }
            }
            cached_response_mutex.unlock();
            delete_old_pixmaps(thread_index, mupdf_context);
            if (*should_quit_pointer) break;

            thread_busy_status[thread_index] = false;
            sleep_ms(100);
            pending_requests_mutex.lock();
        }
        if (*should_quit_pointer) break;
        //cout << "worker thread running ... pending requests: " << pending_render_requests.size() << endl;

        RenderRequest req = pending_render_requests[pending_render_requests.size() - 1];

        // if the request is already rendered, just return the previous result
        cached_response_mutex.lock();

        if (are_documents_invalidated) {
            std::lock_guard<std::mutex> lock(opened_documents_mutex);
            for (auto [_, document] : opened_documents) {
                fz_drop_document(mupdf_context, document);
            }
            opened_documents.clear();
            are_documents_invalidated = false;
        }

        bool is_already_rendered = false;
        for (const auto& cached_rep : cached_responses) {
            if ((cached_rep.request == req) && (cached_rep.invalid == false)) is_already_rendered = true;
        }

        if (!is_already_rendered) {
            RenderResponse resp;
            resp.thread = thread_index;
            resp.request = req;
            resp.last_access_time = QDateTime::currentMSecsSinceEpoch();
            resp.texture = 0;
            resp.invalid = false;
            resp.pending = true;
            cached_responses.push_back(resp);
        }

        cached_response_mutex.unlock();
        pending_render_requests.pop_back();
        pending_requests_mutex.unlock();
        thread_rendering_mutex[thread_index].lock();
        thread_busy_status[thread_index] = true;

        if (!is_already_rendered) {

            fz_try(mupdf_context) {
                fz_matrix transform_matrix = fz_pre_scale(fz_identity, req.zoom_level * req.display_scale, req.zoom_level * req.display_scale);
                fz_document* doc = get_document_with_path(thread_index, mupdf_context, req.path);

                // while this request renders, make sure there is a tiny preview of the page to draw
                // in its place (and in the place of other requests of the page that aren't rendered yet)
                render_preview_if_missing(thread_index, mupdf_context, doc, req);

                fz_pixmap* rendered_pixmap = nullptr;

                if (req.slice_index == -1) {
                    if (req.should_render_annotations) {
                        rendered_pixmap = fz_new_pixmap_from_page_number(mupdf_context, doc, req.page, transform_matrix, fz_device_rgb(mupdf_context), 0);
                    }
                    else {
                        fz_page* page = fz_load_page(mupdf_context, doc, req.page);
                        rendered_pixmap = fz_new_pixmap_from_page_contents(mupdf_context, page, transform_matrix, fz_device_rgb(mupdf_context), 0);
                        fz_drop_page(mupdf_context, page);
                    }
                }
                else {
                    fz_page* page = fz_load_page(mupdf_context, doc, req.page);
                    fz_rect rect = fz_bound_page(mupdf_context, page);

                    fz_irect bbox = get_index_irect(rect, req.slice_index, transform_matrix, req.num_h_slices, req.num_v_slices);

                    rendered_pixmap = fz_new_pixmap_with_bbox(mupdf_context, fz_device_rgb(mupdf_context), bbox, nullptr, 0); // todo: use alpha

                    fz_clear_pixmap_with_value(mupdf_context, rendered_pixmap, 0xFF);
                    fz_device* draw_device = fz_new_draw_device(mupdf_context, transform_matrix, rendered_pixmap);

                    if (req.should_render_annotations) {
                        fz_run_page(mupdf_context, page, draw_device, fz_identity, nullptr); // todo: use cookie to report progress
                    }
                    else {
                        fz_run_page_contents(mupdf_context, page, draw_device, fz_identity, nullptr); // todo: use cookie to report progress
                    }

                    fz_close_device(mupdf_context, draw_device);
                    fz_drop_device(mupdf_context, draw_device);
                    fz_drop_page(mupdf_context, page);

                }

                if (GAMMA != 1.0f) {
                    fz_gamma_pixmap(mupdf_context, rendered_pixmap, GAMMA);
                }

                RenderResponse resp;
                resp.thread = thread_index;
                resp.request = req;
                resp.texture = 0;
                resp.invalid = false;

                cached_response_mutex.lock();
                int index = get_pending_response_index_with_thread_index(req, thread_index);
                if (index >= 0) {
                    cached_responses[index].last_access_time = QDateTime::currentMSecsSinceEpoch();
                    cached_responses[index].pixmap = rendered_pixmap;
                    cached_responses[index].width = rendered_pixmap->w;
                    cached_responses[index].height = rendered_pixmap->h;
                    cached_responses[index].pending = false;
                }

                cached_response_mutex.unlock();

                emit render_advance();

            }
            fz_catch(mupdf_context) {
                // Keep the entry as failed: while it is cached, the page is drawn from the closest
                // texture there is and not rendered again until it is dropped (a while after it
                // failed: see find_rendered_page).
                cached_response_mutex.lock();
                int index = get_pending_response_index_with_thread_index(req, thread_index);
                if (index >= 0) {
                    cached_responses[index].pending = false;
                    cached_responses[index].failed = true;
                    cached_responses[index].last_access_time = QDateTime::currentMSecsSinceEpoch();
                }
                cached_response_mutex.unlock();
                emit render_advance();
                std::cerr << "Error: could not render page" << std::endl;
            }
        }
        thread_rendering_mutex[thread_index].unlock();

    }
}

void PdfRenderer::add_password(std::wstring path, std::string password) {
    document_passwords[path] = password;
    delete_old_pages(true, false);
}

bool operator==(const RenderRequest& lhs, const RenderRequest& rhs) {
    if (rhs.path != lhs.path) {
        return false;
    }
    if (rhs.slice_index != lhs.slice_index) {
        return false;
    }
    if (rhs.num_h_slices != lhs.num_h_slices) {
        return false;
    }
    if (rhs.num_v_slices != lhs.num_v_slices) {
        return false;
    }
    if (rhs.page != lhs.page) {
        return false;
    }
    if (rhs.zoom_level != lhs.zoom_level) {
        return false;
    }
    if (rhs.display_scale != lhs.display_scale) {
        return false;
    }
    if (rhs.should_render_annotations != lhs.should_render_annotations) {
        return false;
    }
    return true;
}


bool PdfRenderer::is_search_busy() {
    return pending_search_request.has_value() || search_is_busy;

}
bool PdfRenderer::is_busy() {
    for (int i = 0; i < num_threads; i++) {
        if (thread_busy_status[i]) {
            return true;
        }
    }
    return pending_render_requests.size() > 0;
}

void PdfRenderer::free_all_resources_for_document(std::wstring doc_path) {
    searching_mutex.lock();
    for (int i = 0; i < num_threads; i++) {
        thread_rendering_mutex[i].lock();
    }
    
    delete_old_pages(true, true); // todo: this is overkill, just delete the pixmaps for the document

    for (int i = 0; i < num_threads; i++) {
        auto index = std::make_pair(i, doc_path);
        if (opened_documents.find(index) != opened_documents.end()) {
            fz_document* doc_to_delete = opened_documents[index];
            fz_drop_document(thread_contexts[i], doc_to_delete);
            opened_documents.erase(index);
        }
    }

    for (int i = 0; i < num_threads; i++) {
        thread_rendering_mutex[i].unlock();
    }
    searching_mutex.unlock();
}

void PdfRenderer::debug() {
    cached_response_mutex.lock();
    for (auto resp : cached_responses) {
        std::wcout << resp.request.path << L" " << resp.request.page << " " << resp.request.slice_index << L" " << resp.request.zoom_level << "(" << resp.width << "*" << resp.height << ")" << std::endl;
    }
    std::wcout << "________________________________________\n";
    cached_response_mutex.unlock();
}

int PdfRenderer::get_pending_response_index_with_thread_index(const RenderRequest& req, int thread_index){
    // assumes we hold a lock on cached_response_mutex

    for (int i = 0; i < cached_responses.size(); i++) {
        if (cached_responses[i].pending && (cached_responses[i].request == req) && (cached_responses[i].thread == thread_index)) {
            return i;
        }
    }
    return -1;
}

void PdfRenderer::set_num_cached_pages(int n_cached_pages) {
    num_cached_pages = n_cached_pages;
}
