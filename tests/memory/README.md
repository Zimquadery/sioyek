# Memory leak tests

`memory_leak_tests.py` looks for memory that sioyek leaks again and again during normal use.
It needs macOS: it uses Apple's `leaks` and `footprint` tools.

```sh
./build_mac.sh                            # the tests use build/sioyek.app
python3 tests/memory/memory_leak_tests.py # all scenarios, about 5 to 10 minutes
python3 tests/memory/memory_leak_tests.py --list
python3 tests/memory/memory_leak_tests.py --scenario popups --iterations 100
```

The exit status is 1 when a scenario fails, so the script can run in CI or before a release.

You can keep using the Mac while it runs. By default (`--window background`) the test copies are
started through LaunchServices without being activated, and are marked as agent apps (no Dock
icon or menu bar), so they never take keyboard focus, and every message to them carries
`--nofocus` (otherwise sioyek raises and activates its window for each one). Their windows
still appear, usually behind yours. macOS doesn't redraw windows that are covered, so in this
mode pages are mostly not rendered, and memory growth that only happens while drawing (page
renders, GPU textures) goes unnoticed: a run in which the test windows were frontmost showed
graphics memory growing with the bookmark list, which background runs don't reproduce. With
`--window hidden` no windows appear at all and nothing is rendered. For full coverage use
`--window foreground` (the window comes to the front and takes focus) when you're away from the
Mac.

## What it does

Each scenario starts its own sioyek and repeats one iteration of user actions through
`--execute-command`:

| Scenario | Repeats |
| --- | --- |
| `windows_open_close` | open four documents as windows, close them with `close_window` |
| `window_switching` | cycle through six windows (`goto_next_tab`) |
| `popups` | command palette, table of contents, file browser, bookmark list and recent documents, each replacing the previous |
| `search` | two searches and stepping through their matches |
| `navigation` | paging, scrolling and zooming (page rendering and its cache) |
| `theme_switch` | toggling dark mode with a popup open |

For each scenario the runner:

1. Runs a few warm-up iterations (`--warmup`), so caches and lazily created objects exist.
2. Saves a baseline memory graph with `leaks --outputGraph` and measures the physical footprint.
3. Runs `--iterations` iterations (default 40), pausing at the halfway checkpoint for a
   `leaks --diffFrom` reading against the same baseline graph.
4. Takes a second `leaks --diffFrom` reading at the end and measures the footprint again.

The two readings are what let the verdict tell *recurring* leaks from *one-off* ones: a leak
that fires in both halves of the run is recurring; a leak that fires at most once is a one-off
(one-off leaks created during warm-up are already in the baseline). A leak here is one leaked
allocation, such as an object that nothing references anymore, together with all the memory
blocks it owned (`leaks` reports the blocks; the runner counts the roots, grouped by allocation
stack).

## The verdict rules (formally verified)

The verdict logic is specified and proved in [`lean/MemoryTest.lean`](lean/MemoryTest.lean)
(Lean 4, no external dependencies; check with `lean tests/memory/lean/MemoryTest.lean`). The
`decide_verdict` function in the runner mirrors `MemoryTest.verdict`. A scenario:

- **fails** when any `leaks` reading produced no parseable summary (instrument failure — never
  silently green, `MemoryTest.fail_on_parse_failure`);
- **fails** when a leak fired in both halves of the run (`both_halves_fail`): every leak that
  recurs at least once per half-run is detected, however small its per-iteration count — the
  detection resolution is "fires in every window of `iterations / 2` iterations"
  (`fired_every_window`);
- **fails** when the total new leak roots reach `--min-new-leaks` (default 3) — a big one-off
  batch;
- **fails** when the physical footprint grew by more than `--max-footprint-growth-mb` (default
  1 MB) per iteration: growth covers memory that is still referenced but never released, such
  as unbounded caches, which `leaks` can't see;
- **passes** otherwise, labeled "ok, one-off leaks" when new leaks were reported. A leak that
  fires exactly once in the whole run can never fail the gate (`single_fire_not_fail`); a
  passing verdict guarantees the instrument was healthy, no leak recurred across halves, the
  one-off batch was below the threshold, and the footprint stayed within budget
  (`pass_soundness`).

The failing verdict is monotone in every counted axis (`fail_monotone`), so the fallback that
counts blocks instead of roots (used when the app copy cannot be signed debuggable) is
conservative: it can only fail more, never less.

For contrast, the rule this suite replaces (borrowed from yaview) failed only when
`newLeaks >= max(3, iterations / 4)`. `MemoryTest.old_rule_blind_spot` proves that a leak
firing on every 5th iteration never fails that rule at *any* iteration count.

## Reading the results

Results go to `tests/memory/results/<date-time>/`, which git ignores, or to the folder given
with `--results`:

- `summary.json`: the numbers and verdict for every scenario.
- `<scenario>-new-leaks.txt`: the `leaks` report of leaks that appeared during the measured
  iterations, with the call stack of each allocation. Look for sioyek functions (`MainWidget::`,
  `BaseSelectorWidget::`, ...) near the top of the stacks.
- `<scenario>-checkpoint-leaks.txt`: the halfway reading (the one-off leaks that happened in the
  first half, which the verdict correctly does not treat as recurring).
- `<scenario>-baseline-footprint.txt`, `<scenario>-final-footprint.txt`: the physical footprint
  by category (malloc, graphics memory, ...). Compare them to see what grew.
- `<scenario>-baseline.memgraph`: the baseline graph. Open it in Xcode's memory graph debugger,
  or inspect it with `leaks`, `heap` or `vmmap` (for example `heap <file>.memgraph`).
- `<scenario>.log`: sioyek's output.

The runner tests a copy of the app, ad-hoc signed with the `get-task-allow` entitlement, which
marks it as debuggable. Without that, macOS lets `leaks` count leaks in a running app but not
save memory graphs or show what leaked. If the copy can't be signed, the runner compares leak
totals instead (conservative, per `fail_monotone`). Allocation stacks come from
`MallocStackLogging=lite`; `--no-stack-logging` is a little faster but the reports then lack
stacks.

The test window is 1000x800 points (set in the test home folder's `prefs_user.config`), so
footprints are comparable between runs; a screen-sized window has a footprint of several GB.

Your own sioyek data is never touched. Each scenario runs with its own throwaway home folder
(`HOME` and `CFFIXED_USER_HOME`), a private `TMPDIR` for the instance socket, a unique instance
name, and `--nofocus`. Test instances are quit normally, falling back to SIGTERM/SIGKILL. A
killed sioyek leaves its single-instance guard's System V shared memory segment behind; macOS
allows only 32 system-wide, and once they're used up every new sioyek, including your own, exits
at startup. The runner removes the segments of instances it had to kill.

## Adding a scenario

Add a `Scenario` to `SCENARIOS` in `memory_leak_tests.py`. Each `Step` is a macro (sioyek
commands separated by `;`), optional `--execute-command-data`, or `open_document=N` to open one
of the test documents (six-page PDFs the runner writes, with a table of contents). Steps that
open a popup must pass `wait=False`: a popup waits for input, so sioyek doesn't answer until it
closes. If a scenario exercises a new code path, consider whether the formal model in
`lean/MemoryTest.lean` still describes the measurement (it does: the verdict only depends on the
two readings, not on what the iterations do).
