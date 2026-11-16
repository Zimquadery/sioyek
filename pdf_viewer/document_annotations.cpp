// Mirror of the document's annotations inside the PDF file itself, enabled by the
// `store_annotations_in_pdf` config option.
//
// The database remains the source of truth: annotation changes are written to the
// database immediately (as before) and queued here; the queue is applied to the PDF
// file with an incremental save which appends only the changed objects and never
// rewrites the file's original bytes.
//
//   - a highlight is a Highlight annotation (Underline for uppercase types, StrikeOut
//     for '_'); its color is the type's color and its note is the annotation contents,
//   - a bookmark is a Text annotation, a freetext bookmark a FreeText annotation and
//     a box bookmark a Square annotation,
//   - a visible portal to the document itself is a Link annotation with a GoTo action
//     to its destination (portals to other documents are not mirrored because the PDF
//     format needs the destination's page index),
//   - marks are destinations in a private /SioyekMarks dictionary of the document
//     catalog, keyed by the mark's symbol.
//
// Every mirrored annotation carries a /SioyekUuid string which maps it to its database
// row. At load time annotations of the managed types are read from the file: ones whose
// uuid exists in the database are attached to their row (so later updates and deletes
// find them), ones whose uuid is unknown are deleted from the file (a deletion whose
// save was interrupted), and ones without a uuid were made by other programs and are
// imported into the database, then stamped so they are recognized afterwards.
//
// Changes are batched and applied in `flush_pdf_annotations` (called periodically and
// at persist points), one incremental save per flush.

#include "document.h"
#include "database.h"
#include "utils.h"

#include <qfileinfo.h>

#include <algorithm>
#include <cctype>
#include <cstring>
#include <set>

extern bool STORE_ANNOTATIONS_IN_PDF;
extern int ANNOTATIONS_PDF_SAVE_PERIOD_MILISECONDS;
extern float BOOKMARK_RECT_SIZE;
extern bool EXACT_HIGHLIGHT_SELECT;

namespace {

    const char* UUID_KEY = "SioyekUuid";
    const char* MARKS_DICT_KEY = "SioyekMarks";

    int64_t current_time_secs() {
        return QDateTime::currentSecsSinceEpoch();
    }

    int64_t annotation_time_secs(const std::string& time) {
        QDateTime datetime = QDateTime::fromString(QString::fromStdString(time), "yyyy-MM-dd HH:mm:ss");
        return datetime.isValid() ? datetime.toSecsSinceEpoch() : current_time_secs();
    }

    // the matrix from PDF user space to page coordinates
    fz_matrix page_transform(fz_context* ctx, pdf_document* pdf, int page_number) {
        fz_matrix ctm = fz_identity;
        pdf_page_obj_transform(ctx, pdf_lookup_page_obj(ctx, pdf, page_number), nullptr, &ctm);
        return ctm;
    }

    // an annotation's /C (or /IC) color as RGB; false when it has none
    bool read_color(fz_context* ctx, pdf_obj* annot, pdf_obj* key, float out_color[3]) {
        pdf_obj* color = pdf_dict_get(ctx, annot, key);
        int n = pdf_array_len(ctx, color);
        if (n == 3) {
            for (int i = 0; i < 3; i++) out_color[i] = pdf_array_get_real(ctx, color, i);
            return true;
        }
        if (n == 1) {
            out_color[0] = out_color[1] = out_color[2] = pdf_array_get_real(ctx, color, 0);
            return true;
        }
        if (n == 4) {
            float k = pdf_array_get_real(ctx, color, 3);
            for (int i = 0; i < 3; i++) out_color[i] = (1 - pdf_array_get_real(ctx, color, i)) * (1 - k);
            return true;
        }
        return false;
    }

    // the destination [page /XYZ left top zoom] of a GoTo action or a mark entry
    struct Destination {
        int page = 0;
        std::optional<float> x;
        std::optional<float> y;
        std::optional<float> zoom_level;
    };

    std::optional<Destination> read_destination(fz_context* ctx, pdf_document* pdf, pdf_obj* dest) {
        if (pdf_is_dict(ctx, dest)) {
            dest = pdf_dict_get(ctx, dest, PDF_NAME(D));
        }
        if (!pdf_is_array(ctx, dest) || pdf_array_len(ctx, dest) < 2) {
            return {};
        }
        Destination res;
        res.page = pdf_lookup_page_number(ctx, pdf, pdf_array_get(ctx, dest, 0));
        if (res.page < 0) {
            return {};
        }
        if (pdf_name_eq(ctx, pdf_array_get(ctx, dest, 1), PDF_NAME(XYZ))) {
            pdf_obj* x = pdf_array_get(ctx, dest, 2);
            pdf_obj* y = pdf_array_get(ctx, dest, 3);
            pdf_obj* zoom = pdf_array_get(ctx, dest, 4);
            if (pdf_is_number(ctx, x)) res.x = pdf_to_real(ctx, x);
            if (pdf_is_number(ctx, y)) res.y = pdf_to_real(ctx, y);
            if (pdf_is_number(ctx, zoom) && pdf_to_real(ctx, zoom) > 0) res.zoom_level = pdf_to_real(ctx, zoom);
        }
        return res;
    }

    // the /SioyekMarks dictionary of the document catalog; nullptr when it doesn't exist
    pdf_obj* marks_dictionary(fz_context* ctx, pdf_document* pdf) {
        pdf_obj* catalog = pdf_dict_get(ctx, pdf_trailer(ctx, pdf), PDF_NAME(Root));
        return pdf_dict_gets(ctx, catalog, MARKS_DICT_KEY);
    }
}

pdf_document* Document::get_pdf_document() {
    return doc ? pdf_specifics(context, doc) : nullptr;
}

bool Document::is_pdf_document() {
    return get_pdf_document() != nullptr;
}

// Appends the changes to the file. An incremental save writes only the changed objects,
// after the original contents, which stay as they were. MuPDF expects one incremental
// save per loaded document: every save truncates the file to its original size and
// writes all of the session's changes again, but the /Prev of the written trailer would
// point at the previous save's xref, which is gone. Resetting startxref makes every
// save's section continue the file's own last xref instead.
bool Document::save_pdf_annotations() {
    pdf_document* pdf_doc = get_pdf_document();
    if (!pdf_doc || !pdf_has_unsaved_changes(context, pdf_doc)) {
        return pdf_doc != nullptr;
    }
    // An incremental save copies the file up to `doc->file_size` (its size at parse
    // time) and appends a section whose /Prev is `doc->startxref`. We reset startxref
    // to the parse-time head so that every save's section continues the file's own
    // last xref instead of the previous save's, whose bytes the copy discards. The
    // capture must happen again whenever the document is (re)loaded, otherwise the
    // saves after a reload would make the sections written before it unreachable.
    if (pdf_last_saved_load_generation != pdf_load_generation) {
        pdf_original_startxref = pdf_doc->startxref;
        pdf_last_saved_load_generation = pdf_load_generation;
    }
    pdf_doc->startxref = pdf_original_startxref;
    pdf_write_options options = pdf_default_write_options;
    options.do_incremental = 1;
    std::string path = utf8_encode(file_name);
    bool saved = true;
    fz_var(saved);
    fz_try(context) {
        pdf_save_document(context, pdf_doc, path.c_str(), &options);
    }
    fz_catch(context) {
        saved = false;
    }
    if (!saved) {
        show_error_message(L"Could not save the annotations to " + file_name + L": " + utf8_decode(fz_caught_message(context)));
    }
    else {
        // the save changed the file's modification time; the baseline moves with it,
        // otherwise every later flush of this load would refuse to save (the mtime
        // guard would take our own save for an external change)
        pdf_load_mtime = QFileInfo(QString::fromStdWString(file_name)).lastModified();
    }
    // our own save is not a change of the document, don't reload it
    last_update_time = QDateTime::currentDateTime();
    return saved;
}

int Document::write_pdf_annotation(int page_number, enum pdf_annot_type type, const Annotation& annotation,
    const std::function<void(pdf_annot*)>& fill) {

    int object_number = 0;
    fz_page* page = nullptr;
    pdf_annot* annot = nullptr;
    fz_var(page);
    fz_var(annot);
    fz_try(context) {
        page = fz_load_page(context, doc, page_number);
        pdf_page* pdf_page = pdf_page_from_fz_page(context, page);
        if (pdf_page) {
            annot = pdf_create_annot(context, pdf_page, type);
            fill(annot);
            pdf_set_annot_creation_date(context, annot, annotation_time_secs(annotation.creation_time));
            pdf_set_annot_modification_date(context, annot, annotation_time_secs(annotation.modification_time));
            pdf_dict_puts_drop(context, pdf_annot_obj(context, annot), UUID_KEY,
                pdf_new_string(context, annotation.uuid.c_str(), annotation.uuid.size()));
            // the appearance stream makes the annotation visible in readers that don't draw annotations themselves
            pdf_update_annot(context, annot);
            object_number = pdf_to_num(context, pdf_annot_obj(context, annot));
        }
    }
    fz_always(context) {
        pdf_drop_annot(context, annot);
        fz_drop_page(context, page);
    }
    fz_catch(context) {
        object_number = 0;
    }
    return object_number;
}

int Document::write_pdf_highlight(const Highlight& highlight) {
    if (highlight.highlight_rects.size() == 0) {
        return 0;
    }

    DocumentPos begin = absolute_to_page_pos(highlight.selection_begin);
    std::vector<fz_quad> quads;
    for (const AbsoluteRect& rect : highlight.highlight_rects) {
        quads.push_back(fz_quad_from_rect(rect.to_document(this).rect));
    }
    enum pdf_annot_type type = PDF_ANNOT_HIGHLIGHT;
    if (highlight.type == '_') type = PDF_ANNOT_STRIKE_OUT;
    else if (std::isupper(static_cast<unsigned char>(highlight.type))) type = PDF_ANNOT_UNDERLINE;
    std::string note = utf8_encode(highlight.text_annot);

    return write_pdf_annotation(begin.page, type, highlight, [&](pdf_annot* annot) {
        pdf_set_annot_quad_points(context, annot, quads.size(), quads.data());
        pdf_set_annot_color(context, annot, 3, get_highlight_type_color(highlight.type));
        if (note.size() > 0) {
            pdf_set_annot_contents(context, annot, note.c_str());
        }
        });
}

int Document::write_pdf_bookmark(const BookMark& bookmark) {
    // plain bookmarks have no on-page position, no PDF annotation represents them
    if (!bookmark.is_marked() && !bookmark.is_freetext() && !bookmark.is_box()) return 0;
    BookMark bookmark_copy = bookmark;
    DocumentPos begin = absolute_to_page_pos(bookmark_copy.begin_pos());
    std::string description = utf8_encode(bookmark_copy.description);
    PagelessDocumentRect rect;
    enum pdf_annot_type type;

    if (bookmark_copy.is_marked()) {
        type = PDF_ANNOT_TEXT;
        rect = fz_make_rect(begin.x - BOOKMARK_RECT_SIZE, begin.y - BOOKMARK_RECT_SIZE,
            begin.x + BOOKMARK_RECT_SIZE, begin.y + BOOKMARK_RECT_SIZE);
    }
    else {
        type = bookmark_copy.is_box() ? PDF_ANNOT_SQUARE : PDF_ANNOT_FREE_TEXT;
        rect = bookmark_copy.rect().to_document(this).rect;
    }

    return write_pdf_annotation(begin.page, type, bookmark, [&](pdf_annot* annot) {
        pdf_set_annot_rect(context, annot, rect);
        pdf_set_annot_contents(context, annot, description.c_str());
        if (type == PDF_ANNOT_SQUARE) {
            std::optional<char> box_type = bookmark.get_type();
            pdf_set_annot_color(context, annot, 3, get_highlight_type_color(box_type.value_or('a')));
            pdf_set_annot_border_width(context, annot, 1);
        }
        else if (type == PDF_ANNOT_FREE_TEXT) {
            std::string font_face = bookmark.font_face.size() > 0 ? utf8_encode(bookmark.font_face) : "Helv";
            pdf_set_annot_default_appearance(context, annot, font_face.c_str(), bookmark.font_size, 3, bookmark.color);
        }
        });
}

int Document::write_pdf_portal(const Portal& portal) {
    // portals to other documents are not mirrored: a remote GoTo destination needs the
    // destination document's page index, which we don't know without opening it.
    // portals created before x-offsets were tracked have no source position either.
    if (!portal.is_visible() || !portal.src_offset_x.has_value() || (portal.dst.document_checksum != get_checksum())) {
        return 0;
    }

    DocumentPos src = absolute_to_page_pos(AbsoluteDocumentPos{ portal.src_offset_x.value(), portal.src_offset_y });
    int object_number = 0;
    pdf_page* pdf_page = nullptr;
    fz_page* page = nullptr;
    pdf_obj* link = nullptr;
    fz_var(page);
    fz_var(link);
    fz_try(context) {
        page = fz_load_page(context, doc, src.page);
        pdf_page = pdf_page_from_fz_page(context, page);
        if (pdf_page) {
            fz_matrix ctm;
            pdf_page_transform(context, pdf_page, nullptr, &ctm);
            fz_rect rect = fz_make_rect(src.x - BOOKMARK_RECT_SIZE, src.y - BOOKMARK_RECT_SIZE,
                src.x + BOOKMARK_RECT_SIZE, src.y + BOOKMARK_RECT_SIZE);
            rect = fz_transform_rect(rect, fz_invert_matrix(ctm));

            link = pdf_add_new_dict(context, pdf_page->doc, 8);
            pdf_dict_put(context, link, PDF_NAME(Type), PDF_NAME(Annot));
            pdf_dict_put(context, link, PDF_NAME(Subtype), PDF_NAME(Link));
            pdf_dict_put_rect(context, link, PDF_NAME(Rect), rect);
            pdf_dict_puts_drop(context, link, UUID_KEY,
                pdf_new_string(context, portal.uuid.c_str(), portal.uuid.size()));
            pdf_dict_put_date(context, link, PDF_NAME(CreationDate), annotation_time_secs(portal.creation_time));
            pdf_dict_put_date(context, link, PDF_NAME(M), annotation_time_secs(portal.modification_time));
            // no border: sioyek draws the portal itself, other readers show a plain link
            pdf_obj* border = pdf_dict_put_array(context, link, PDF_NAME(Border), 3);
            for (int i = 0; i < 3; i++) pdf_array_push_int(context, border, 0);

            // the action: a GoTo destination to this document's destination position
            DocumentPos dst_page_pos = absolute_to_page_pos(AbsoluteDocumentPos{
                portal.dst.book_state.offset_x, portal.dst.book_state.offset_y });
            fz_point dst_pdf_point = fz_transform_point(fz_make_point(dst_page_pos.x, dst_page_pos.y),
                fz_invert_matrix(page_transform(context, pdf_page->doc, dst_page_pos.page)));

            pdf_obj* action = pdf_dict_put_dict(context, link, PDF_NAME(A), 3);
            pdf_dict_put(context, action, PDF_NAME(S), PDF_NAME(GoTo));
            pdf_obj* dest = pdf_new_array(context, pdf_page->doc, 5);
            pdf_array_push(context, dest, pdf_lookup_page_obj(context, pdf_page->doc, dst_page_pos.page));
            pdf_array_push(context, dest, PDF_NAME(XYZ));
            pdf_array_push_real(context, dest, dst_pdf_point.x);
            pdf_array_push_real(context, dest, dst_pdf_point.y);
            if (portal.dst.book_state.zoom_level > 0) {
                pdf_array_push_real(context, dest, portal.dst.book_state.zoom_level);
            }
            else {
                pdf_array_push(context, dest, PDF_NULL);
            }
            pdf_dict_put_drop(context, action, PDF_NAME(D), dest);

            pdf_obj* annots = pdf_dict_get(context, pdf_page->obj, PDF_NAME(Annots));
            if (!pdf_is_array(context, annots)) {
                annots = pdf_dict_put_array(context, pdf_page->obj, PDF_NAME(Annots), 1);
            }
            pdf_array_push(context, annots, link);
            object_number = pdf_to_num(context, link);
        }
    }
    fz_always(context) {
        pdf_drop_obj(context, link);
        fz_drop_page(context, page);
    }
    fz_catch(context) {
        object_number = 0;
    }
    return object_number;
}

bool Document::write_pdf_mark(const Mark& mark) {
    pdf_document* pdf_doc = get_pdf_document();
    // marks without a uuid (they predate uuid tracking) are not mirrored
    if (!pdf_doc || mark.uuid.size() == 0) return true;
    DocumentPos pos = absolute_to_page_pos(AbsoluteDocumentPos{ mark.x_offset.value_or(0.0f), mark.y_offset });
    std::string name(1, mark.symbol);
    bool written = true;
    fz_var(written);
    fz_try(context) {
        pdf_obj* catalog = pdf_dict_get(context, pdf_trailer(context, pdf_doc), PDF_NAME(Root));
        pdf_obj* marks_dict = pdf_dict_gets(context, catalog, MARKS_DICT_KEY);
        if (!pdf_is_dict(context, marks_dict)) {
            // an indirect dictionary, so that a mark rewrites only this dictionary and not the catalog
            marks_dict = pdf_add_new_dict(context, pdf_doc, 4);
            pdf_dict_puts_drop(context, catalog, MARKS_DICT_KEY, marks_dict);
        }
        pdf_obj* entry = pdf_dict_puts_dict(context, marks_dict, name.c_str(), 3);
        pdf_obj* dest = pdf_new_array(context, pdf_doc, 5);
        pdf_array_push(context, dest, pdf_lookup_page_obj(context, pdf_doc, pos.page));
        pdf_array_push(context, dest, PDF_NAME(XYZ));
        // the destination is in PDF user space, the mark's position is in page coordinates
        fz_point pdf_point = fz_transform_point(fz_make_point(pos.x, pos.y),
            fz_invert_matrix(page_transform(context, pdf_doc, pos.page)));
        if (mark.x_offset.has_value()) {
            pdf_array_push_real(context, dest, pdf_point.x);
        }
        else {
            pdf_array_push(context, dest, PDF_NULL);
        }
        pdf_array_push_real(context, dest, pdf_point.y);
        if (mark.zoom_level.has_value() && mark.zoom_level.value() > 0) {
            pdf_array_push_real(context, dest, mark.zoom_level.value());
        }
        else {
            pdf_array_push(context, dest, PDF_NULL);
        }
        pdf_dict_put_drop(context, entry, PDF_NAME(D), dest);
        pdf_dict_puts_drop(context, entry, UUID_KEY,
            pdf_new_string(context, mark.uuid.c_str(), mark.uuid.size()));
    }
    fz_catch(context) {
        show_error_message(L"Could not save the mark to " + file_name + L": " + utf8_decode(fz_caught_message(context)));
        written = false;
    }
    return written;
}

bool Document::erase_pdf_marks(char symbol) {
    pdf_document* pdf_doc = get_pdf_document();
    if (!pdf_doc) return false;
    bool erased = true;
    fz_var(erased);
    fz_try(context) {
        pdf_obj* marks_dict = marks_dictionary(context, pdf_doc);
        if (pdf_is_dict(context, marks_dict)) {
            std::string name(1, symbol);
            pdf_dict_dels(context, marks_dict, name.c_str());
        }
    }
    fz_catch(context) {
        erased = false;
    }
    return erased;
}

// Deletes the annotation with `pdf_object` from `page_number`. Link annotations
// (portals) are not in MuPDF's annotation list and are removed from the page's
// /Annots array instead. Deleting an annotation which is not there (it was deleted
// by an earlier attempt or lives on another page after a move) succeeds: deletes
// must be idempotent, otherwise a failed save could never be retried.
bool Document::delete_pdf_annotation(int page_number, int pdf_object) {
    bool deleted = true;
    fz_page* page = nullptr;
    fz_var(page);
    fz_try(context) {
        page = fz_load_page(context, doc, page_number);
        pdf_page* pdf_page = pdf_page_from_fz_page(context, page);
        if (pdf_page) {
            for (pdf_annot* annot = pdf_first_annot(context, pdf_page); annot; annot = pdf_next_annot(context, annot)) {
                if (pdf_to_num(context, pdf_annot_obj(context, annot)) == pdf_object) {
                    pdf_delete_annot(context, pdf_page, annot);
                    break;
                }
            }
            pdf_obj* annots = pdf_dict_get(context, pdf_page->obj, PDF_NAME(Annots));
            int num_annots = pdf_array_len(context, annots);
            for (int i = 0; i < num_annots; i++) {
                if (pdf_to_num(context, pdf_array_get(context, annots, i)) == pdf_object) {
                    pdf_array_delete(context, annots, i);
                    break;
                }
            }
        }
    }
    fz_always(context) {
        fz_drop_page(context, page);
    }
    fz_catch(context) {
        deleted = false;
    }
    return deleted;
}

// Records our uuid on an annotation made by another program, so that it is
// recognized as mirrored on the next load.
bool Document::stamp_pdf_annotation_uuid(int pdf_object, const std::string& uuid) {
    bool stamped = true;
    fz_var(stamped);
    fz_try(context) {
        pdf_document* pdf_doc = get_pdf_document();
        if (pdf_doc) {
            pdf_obj* annot = pdf_load_object(context, pdf_doc, pdf_object);
            pdf_dict_puts_drop(context, annot, UUID_KEY,
                pdf_new_string(context, uuid.c_str(), uuid.size()));
            pdf_drop_obj(context, annot);
        }
        else {
            stamped = false;
        }
    }
    fz_catch(context) {
        stamped = false;
    }
    return stamped;
}

void Document::queue_pdf_annotation_write(const Annotation& annotation) {
    if (!STORE_ANNOTATIONS_IN_PDF || !is_pdf_document()) return;
    // annotations which are already mirrored are rewritten at flush time
    if (std::find(pdf_pending_writes.begin(), pdf_pending_writes.end(), annotation.uuid) == pdf_pending_writes.end()) {
        pdf_pending_writes.push_back(annotation.uuid);
    }
}

void Document::queue_pdf_annotation_delete(int page, int pdf_object) {
    if (!STORE_ANNOTATIONS_IN_PDF || !is_pdf_document() || (pdf_object == 0)) return;
    pdf_pending_deletions.push_back({ page, pdf_object });
}

void Document::queue_pdf_mark_write(char symbol) {
    if (!STORE_ANNOTATIONS_IN_PDF || !is_pdf_document()) return;
    if (std::find(pdf_pending_mark_writes.begin(), pdf_pending_mark_writes.end(), symbol) == pdf_pending_mark_writes.end()) {
        pdf_pending_mark_writes.push_back(symbol);
    }
}

void Document::queue_pdf_mark_delete(char symbol) {
    if (!STORE_ANNOTATIONS_IN_PDF || !is_pdf_document()) return;
    if (std::find(pdf_pending_mark_deletes.begin(), pdf_pending_mark_deletes.end(), symbol) == pdf_pending_mark_deletes.end()) {
        pdf_pending_mark_deletes.push_back(symbol);
    }
}

bool Document::has_pending_pdf_annotation_changes() {
    return (pdf_pending_writes.size() > 0) ||
        (pdf_pending_deletions.size() > 0) ||
        (pdf_pending_mark_writes.size() > 0) ||
        (pdf_pending_mark_deletes.size() > 0) ||
        (pdf_pending_uuid_stamps.size() > 0);
}

// Applies the staged results of the page-dimensions thread's ingest to the document
// state (which is only touched on the main thread). The database inserts happen here,
// on the main thread, only for imports that pass the duplicate filter below: the
// ingest thread classifies the file as it was at load time and cannot know whether
// an unstamped annotation it sees is one we already imported but whose stamp save
// failed, so the final decision is deferred to this filter (a re-import would
// duplicate the database row).
void Document::apply_ingested_pdf_annotations() {
    if (!pdf_ingest_result_ready.exchange(false)) return;

    std::vector<PdfIngestedAnnotations> results;
    {
        std::lock_guard<std::mutex> lock(pdf_ingest_mutex);
        // a document reload can ingest more than once before the first apply
        results = std::move(pdf_ingest_results);
        pdf_ingest_results.clear();
    }

    std::set<int> batch_imports;
    auto import_is_duplicate = [&](int object) {
        if (object == 0) return false;
        if (batch_imports.count(object) > 0) return true;
        for (const auto& [pending_object, _] : pdf_pending_uuid_stamps) {
            if (pending_object == object) return true;
        }
        for (const auto& highlight : highlights) {
            if (highlight.pdf_object == object) return true;
        }
        for (const auto& bookmark : bookmarks) {
            if (bookmark.pdf_object == object) return true;
        }
        for (const auto& portal : portals) {
            if (portal.pdf_object == object) return true;
        }
        return false;
    };

    for (auto& result : results) {
        for (auto& highlight : result.highlights) {
            if (import_is_duplicate(highlight.pdf_object)) continue;
            db_manager->insert_highlight_with_annotation(get_checksum(), highlight.description, highlight.text_annot,
                highlight.selection_begin.x, highlight.selection_begin.y,
                highlight.selection_end.x, highlight.selection_end.y,
                highlight.type, utf8_decode(highlight.uuid));
            pdf_pending_uuid_stamps.push_back({ highlight.pdf_object, highlight.uuid });
            batch_imports.insert(highlight.pdf_object);
            highlights.push_back(std::move(highlight));
        }
        for (auto& bookmark : result.bookmarks) {
            if (import_is_duplicate(bookmark.pdf_object)) continue;
            if (bookmark.is_freetext() || bookmark.is_box()) {
                db_manager->insert_bookmark_freetext(get_checksum(), bookmark);
            }
            else {
                db_manager->insert_bookmark_marked(get_checksum(), bookmark.description,
                    bookmark.begin_x, bookmark.begin_y, utf8_decode(bookmark.uuid));
            }
            pdf_pending_uuid_stamps.push_back({ bookmark.pdf_object, bookmark.uuid });
            batch_imports.insert(bookmark.pdf_object);
            bookmarks.push_back(std::move(bookmark));
        }
        for (auto& mark : result.marks) {
            if (get_mark_index(mark.symbol) == -1) {
                db_manager->insert_mark(get_checksum(), mark.symbol, mark.y_offset, utf8_decode(mark.uuid),
                    mark.x_offset, mark.zoom_level);
                marks.push_back(std::move(mark));
            }
        }
        for (auto& [uuid, object] : result.attaches) {
            for (auto& highlight : highlights) {
                if (highlight.uuid == uuid) { highlight.pdf_object = object; break; }
            }
            for (auto& bookmark : bookmarks) {
                if (bookmark.uuid == uuid) { bookmark.pdf_object = object; break; }
            }
            for (auto& portal : portals) {
                if (portal.uuid == uuid) { portal.pdf_object = object; break; }
            }
        }
        for (auto& [page, object] : result.deletions) {
            pdf_pending_deletions.push_back({ page, object });
        }
        for (char symbol : result.mark_deletes) {
            if (std::find(pdf_pending_mark_deletes.begin(), pdf_pending_mark_deletes.end(), symbol) == pdf_pending_mark_deletes.end()) {
                pdf_pending_mark_deletes.push_back(symbol);
            }
        }
        if (result.annotations_dirty) {
            is_annotations_dirty = true;
        }
    }
}

bool Document::flush_pdf_annotations(bool force) {
    apply_ingested_pdf_annotations();
    if (!STORE_ANNOTATIONS_IN_PDF || !is_pdf_document()) return false;
    if (!force) {
        if (!has_pending_pdf_annotation_changes()) return false;
        // a failed save stops the periodic flush until the next forced one (e.g. close)
        if (pdf_save_failed) return false;
        if (pdf_mtime_refused) {
            if (pdf_load_mtime != pdf_refusal_mtime) {
                // the watcher reloaded the document since the refusal, the baseline is
                // fresh again and the periodic flush can resume
                pdf_mtime_refused = false;
            }
            else {
                return false;
            }
        }
        if (pdf_last_flush_datetime.isValid()) {
            QDateTime now = QDateTime::currentDateTime();
            if (pdf_last_flush_datetime.msecsTo(now) < ANNOTATIONS_PDF_SAVE_PERIOD_MILISECONDS) return false;
        }
    }
    // an incremental save appends to the file as it is on disk now; if the file changed
    // since we loaded it (e.g. a LaTeX rebuild), appending would corrupt it. Don't bump
    // last_update_time so that the watcher reloads the document instead. Without a
    // baseline (documents whose load skipped the capture) we cannot detect changes and
    // save as before.
    if (pdf_load_mtime.isValid() && (QFileInfo(QString::fromStdWString(file_name)).lastModified() != pdf_load_mtime)) {
        if (!pdf_mtime_refused) {
            show_error_message(L"The annotations were not saved to " + file_name +
                L" because it changed on disk and is about to be reloaded");
        }
        pdf_refusal_mtime = pdf_load_mtime;
        pdf_mtime_refused = true;
        return false;
    }

    bool res = true;

    for (auto [object, uuid] : pdf_pending_uuid_stamps) {
        res = res && stamp_pdf_annotation_uuid(object, uuid);
    }

    for (auto [page, object] : pdf_pending_deletions) {
        res = res && delete_pdf_annotation(page, object);
    }

    // deletions first, so that re-marking a deleted symbol wins
    for (char symbol : pdf_pending_mark_deletes) {
        res = res && erase_pdf_marks(symbol);
    }

    // an annotation which is already mirrored is rewritten (delete + create)
    for (const std::string& uuid : pdf_pending_writes) {
        int highlight_index = find_highlight_index_with_uuid(uuid);
        if (highlight_index > -1) {
            Highlight& highlight = highlights[highlight_index];
            int page = absolute_to_page_pos(highlight.selection_begin).page;
            res = res && (!highlight.pdf_object || delete_pdf_annotation(page, highlight.pdf_object));
            highlight.pdf_object = write_pdf_highlight(highlight);
            continue;
        }

        for (size_t i = 0; i < bookmarks.size(); i++) {
            if (bookmarks[i].uuid == uuid) {
                BookMark& bookmark = bookmarks[i];
                int page = get_offset_page_number(bookmark.get_y_offset());
                res = res && (!bookmark.pdf_object || delete_pdf_annotation(page, bookmark.pdf_object));
                bookmark.pdf_object = write_pdf_bookmark(bookmark);
                break;
            }
        }

        for (size_t i = 0; i < portals.size(); i++) {
            if (portals[i].uuid == uuid) {
                Portal& portal = portals[i];
                int page = get_offset_page_number(portal.src_offset_y);
                res = res && (!portal.pdf_object || delete_pdf_annotation(page, portal.pdf_object));
                portal.pdf_object = write_pdf_portal(portal);
                break;
            }
        }
    }

    for (char symbol : pdf_pending_mark_writes) {
        std::optional<Mark> mark = get_mark_if_exists(symbol);
        if (mark.has_value()) {
            res = res && write_pdf_mark(mark.value());
        }
        else {
            res = res && erase_pdf_marks(symbol);
        }
    }

    if (res) {
        res = save_pdf_annotations();
    }

    pdf_last_flush_datetime = QDateTime::currentDateTime();
    if (res) {
        pdf_pending_writes.clear();
        pdf_pending_deletions.clear();
        pdf_pending_mark_writes.clear();
        pdf_pending_mark_deletes.clear();
        pdf_pending_uuid_stamps.clear();
        pdf_save_failed = false;
        pdf_mtime_refused = false;
    }
    else {
        // the pending changes stay queued and are retried at the next forced flush;
        // the periodic flush is stopped until then to avoid repeating a failing save
        if (!pdf_save_failed) {
            show_error_message(L"Could not save the annotation changes to " + file_name);
        }
        pdf_save_failed = true;
    }
    return res;
}

// Reads the annotations of the managed types from the PDF file and reconciles them
// with the database-loaded annotations: mirrored ones are attached to their rows (so
// later updates and deletes find them), ones with an unknown uuid are orphans of
// interrupted deletions and are removed on the next flush, and ones without a uuid
// were made by other programs and are imported into the database and stamped.
// Runs in the page-dimensions background thread; `page_widths` and `page_y_offsets`
// place the pages in absolute document coordinates. The document state is only mutated
// on the main thread: the ingest stages everything it produces in `pdf_ingest_results`
// and apply_ingested_pdf_annotations applies it (the database inserts happen there, on
// the mutex-protected DatabaseManager).
void Document::ingest_pdf_annotations(fz_context* thread_context, fz_document* thread_document,
    const std::vector<float>& page_widths, const std::vector<float>& page_y_offsets) {

    if (!STORE_ANNOTATIONS_IN_PDF || (page_widths.size() == 0)) return;
    pdf_document* pdf_doc = nullptr;
    fz_try(thread_context) {
        pdf_doc = pdf_specifics(thread_context, thread_document);
    }
    fz_catch(thread_context) {
        pdf_doc = nullptr;
    }
    if (!pdf_doc) return;

    PdfIngestedAnnotations result;

    std::set<std::string> known_uuids;
    for (const auto& mark : marks) if (mark.uuid.size() > 0) known_uuids.insert(mark.uuid);
    for (const auto& bookmark : bookmarks) if (bookmark.uuid.size() > 0) known_uuids.insert(bookmark.uuid);
    for (const auto& highlight : highlights) if (highlight.uuid.size() > 0) known_uuids.insert(highlight.uuid);
    for (const auto& portal : portals) if (portal.uuid.size() > 0) known_uuids.insert(portal.uuid);

    int num_pages = static_cast<int>(page_widths.size());
    for (int page_number = 0; page_number < num_pages; page_number++) {
        fz_page* page = nullptr;
        fz_var(page);
        fz_try(thread_context) {
            page = fz_load_page(thread_context, thread_document, page_number);
            pdf_page* pdf_page = page ? pdf_page_from_fz_page(thread_context, page) : nullptr;
            if (pdf_page) {
                float page_width = page_widths[page_number];
                float page_y_offset = page_y_offsets[page_number];
                fz_matrix ctm;
                pdf_page_transform(thread_context, pdf_page, nullptr, &ctm);
                auto to_absolute = [&](fz_rect rect) {
                    rect = fz_transform_rect(rect, ctm);
                    return AbsoluteRect(
                        AbsoluteDocumentPos{ rect.x0 - page_width / 2, rect.y0 + page_y_offset },
                        AbsoluteDocumentPos{ rect.x1 - page_width / 2, rect.y1 + page_y_offset });
                };

                pdf_obj* annots = pdf_dict_get(thread_context, pdf_page->obj, PDF_NAME(Annots));
                int num_annots = pdf_array_len(thread_context, annots);
                for (int i = 0; i < num_annots; i++) {
                    pdf_obj* annot = pdf_array_get(thread_context, annots, i);
                    if (!pdf_is_dict(thread_context, annot)) continue;
                    int object_number = pdf_to_num(thread_context, annot);
                    if (object_number == 0) continue;

                    // a damaged annotation must not abort the read of the others
                    fz_try(thread_context) {
                        pdf_obj* uuid_obj = pdf_dict_gets(thread_context, annot, UUID_KEY);
                        const char* uuid = uuid_obj ? pdf_to_str_buf(thread_context, uuid_obj) : nullptr;
                        bool has_uuid = uuid && (uuid[0] != '\0');
                        pdf_obj* subtype = pdf_dict_get(thread_context, annot, PDF_NAME(Subtype));
                        bool is_highlight = pdf_name_eq(thread_context, subtype, PDF_NAME(Highlight));
                        bool is_underline = pdf_name_eq(thread_context, subtype, PDF_NAME(Underline));
                        bool is_strikeout = pdf_name_eq(thread_context, subtype, PDF_NAME(StrikeOut));
                        bool is_text = pdf_name_eq(thread_context, subtype, PDF_NAME(Text));
                        bool is_freetext = pdf_name_eq(thread_context, subtype, PDF_NAME(FreeText));
                        bool is_square = pdf_name_eq(thread_context, subtype, PDF_NAME(Square));
                        bool is_link = pdf_name_eq(thread_context, subtype, PDF_NAME(Link));
                        bool is_managed = is_highlight || is_underline || is_strikeout || is_text || is_freetext || is_square || is_link;

                        if (is_managed && has_uuid && known_uuids.count(uuid)) {
                            result.attaches.push_back({ uuid, object_number });
                        }
                        else if (is_managed && has_uuid) {
                            // our annotation whose database row is gone; remove it from the file
                            result.deletions.push_back({ page_number, object_number });
                        }
                        else if (is_managed && !has_uuid && !is_link) {
                            // an annotation made by another program: import it into the
                            // database (an unstamped link is the document's own, not a portal)
                            int64_t creation_date = -1;
                            pdf_obj* date = pdf_dict_get(thread_context, annot, PDF_NAME(CreationDate));
                            if (date) creation_date = pdf_to_date(thread_context, date);

                            if (is_highlight || is_underline || is_strikeout) {
                            pdf_obj* quad_points = pdf_dict_get(thread_context, annot, PDF_NAME(QuadPoints));
                            int num_quads = pdf_array_len(thread_context, quad_points) / 8;
                            if (num_quads > 0) {
                                Highlight highlight;
                                for (int q = 0; q < num_quads; q++) {
                                    highlight.highlight_rects.push_back(to_absolute(fz_rect_from_quad(pdf_to_quad(thread_context, quad_points, q * 8))));
                                }
                                const AbsoluteRect& first = highlight.highlight_rects.front();
                                const AbsoluteRect& last = highlight.highlight_rects.back();
                                highlight.selection_begin = { first.x0, (first.y0 + first.y1) / 2 };
                                highlight.selection_end = { last.x1, (last.y0 + last.y1) / 2 };
                                highlight.text_annot = utf8_decode(pdf_dict_get_text_string(thread_context, annot, PDF_NAME(Contents)));
                                float color[3] = { 0, 0, 0 };
                                highlight.type = read_color(thread_context, annot, PDF_NAME(C), color) ? get_highlight_color_type(color) : 'a';
                                if (is_underline) highlight.type = highlight.type - 'a' + 'A';
                                if (is_strikeout) highlight.type = '_';
                                if ((highlight.type != '_') && (!std::isalpha(static_cast<unsigned char>(highlight.type)))) {
                                    highlight.type = 'a';
                                }
                                if (creation_date >= 0) {
                                    highlight.creation_time = QDateTime::fromSecsSinceEpoch(creation_date).toString("yyyy-MM-dd HH:mm:ss").toStdString();
                                }
                                else {
                                    highlight.update_creation_time();
                                }
                                highlight.uuid = new_uuid_utf8();
                                highlight.pdf_object = object_number;
                                std::deque<AbsoluteRect> selected_characters;
                                std::wstring description;
                                get_text_selection(thread_context, highlight.selection_begin, highlight.selection_end,
                                    !EXACT_HIGHLIGHT_SELECT, selected_characters, description, thread_document);
                                highlight.description = description;
                                result.highlights.push_back(std::move(highlight));
                                result.annotations_dirty = true;
                            }
                        }
                        else if (is_text || is_freetext || is_square) {
                            AbsoluteRect rect = to_absolute(pdf_dict_get_rect(thread_context, annot, PDF_NAME(Rect)));
                            BookMark bookmark;
                            bookmark.description = utf8_decode(pdf_dict_get_text_string(thread_context, annot, PDF_NAME(Contents)));
                            bookmark.uuid = new_uuid_utf8();
                            bookmark.pdf_object = object_number;

                            if (is_text) {
                                bookmark.begin_x = (rect.x0 + rect.x1) / 2;
                                bookmark.begin_y = (rect.y0 + rect.y1) / 2;
                                bookmark.y_offset_ = bookmark.begin_y;
                            }
                            else {
                                bookmark.begin_x = rect.x0;
                                bookmark.begin_y = rect.y0;
                                bookmark.end_x = rect.x1;
                                bookmark.end_y = rect.y1;
                                bookmark.y_offset_ = rect.y0;
                            }
                            if (is_square && (bookmark.description.size() == 0 || bookmark.description[0] != L'#')) {
                                // a box bookmark's description starts with '#' and its type
                                float color[3] = { 0, 0, 0 };
                                char type = read_color(thread_context, annot, PDF_NAME(C), color) ? get_highlight_color_type(color) : 'a';
                                std::wstring prefix = L"#";
                                prefix.push_back(type);
                                bookmark.description = bookmark.description.size() > 0 ? prefix + L" " + bookmark.description : prefix;
                            }
                            if (is_freetext) {
                                const char* font = nullptr;
                                int num_components = 0;
                                float text_color[4] = { 0, 0, 0, 0 };
                                pdf_parse_default_appearance(thread_context,
                                    pdf_to_str_buf(thread_context, pdf_dict_get_inheritable(thread_context, annot, PDF_NAME(DA))),
                                    &font, &bookmark.font_size, &num_components, text_color);
                                if (num_components == 3) {
                                    std::copy(text_color, text_color + 3, bookmark.color);
                                }
                                else if (num_components == 1) {
                                    bookmark.color[0] = bookmark.color[1] = bookmark.color[2] = text_color[0];
                                }
                                if (font) bookmark.font_face = utf8_decode(font);
                                if (bookmark.font_size <= 0) bookmark.font_size = -1;
                            }
                            if (creation_date >= 0) {
                                bookmark.creation_time = QDateTime::fromSecsSinceEpoch(creation_date).toString("yyyy-MM-dd HH:mm:ss").toStdString();
                            }
                            else {
                                bookmark.update_creation_time();
                            }
                            result.bookmarks.push_back(std::move(bookmark));
                            result.annotations_dirty = true;
                        }
                        }
                    }
                    fz_catch(thread_context) {
                    }
                }
            }
        }
        fz_always(thread_context) {
            if (page) fz_drop_page(thread_context, page);
        }
        fz_catch(thread_context) {
        }
    }

    // marks: entries of the private /SioyekMarks dictionary of the document catalog
    fz_try(thread_context) {
        pdf_obj* marks_dict = marks_dictionary(thread_context, pdf_doc);
        if (pdf_is_dict(thread_context, marks_dict)) {
            int num_marks = pdf_dict_len(thread_context, marks_dict);
            for (int i = 0; i < num_marks; i++) {
                const char* name = pdf_to_name(thread_context, pdf_dict_get_key(thread_context, marks_dict, i));
                pdf_obj* entry = pdf_dict_get_val(thread_context, marks_dict, i);
                if (!entry || strlen(name) != 1) continue;
                char symbol = name[0];
                pdf_obj* uuid_obj = pdf_dict_gets(thread_context, entry, UUID_KEY);
                const char* uuid = uuid_obj ? pdf_to_str_buf(thread_context, uuid_obj) : nullptr;
                if (uuid && (uuid[0] != '\0')) {
                    if (!known_uuids.count(uuid)) {
                        // our mark whose database row is gone; remove the entry
                        if (std::find(result.mark_deletes.begin(), result.mark_deletes.end(), symbol) == result.mark_deletes.end()) {
                            result.mark_deletes.push_back(symbol);
                        }
                    }
                    continue;
                }
                // a mark made elsewhere (or by an unstamped older version): import it
                // (the database insert happens in apply_ingested_pdf_annotations, which
                // checks the symbol against the live marks)
                std::optional<Destination> destination = read_destination(thread_context, pdf_doc, entry);
                if (!destination || !destination->y || (destination->page >= static_cast<int>(page_widths.size()))) continue;
                fz_point point = fz_transform_point(fz_make_point(destination->x.value_or(0.0f), destination->y.value()),
                    page_transform(thread_context, pdf_doc, destination->page));
                Mark mark;
                mark.symbol = symbol;
                mark.uuid = new_uuid_utf8();
                mark.y_offset = point.y + page_y_offsets[destination->page];
                if (destination->x.has_value()) {
                    mark.x_offset = point.x - page_widths[destination->page] / 2;
                }
                mark.zoom_level = destination->zoom_level;
                mark.update_creation_time();
                result.marks.push_back(std::move(mark));
                result.annotations_dirty = true;
            }
        }
    }
    fz_catch(thread_context) {
    }

    {
        std::lock_guard<std::mutex> lock(pdf_ingest_mutex);
        pdf_ingest_results.push_back(std::move(result));
    }
    pdf_ingest_result_ready = true;
}
