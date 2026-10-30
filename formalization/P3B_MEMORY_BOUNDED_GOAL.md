# P3-B resubmission: bounded memory and preserved progress

**Completed and accepted on 28 October 2026.** The execution contract below
is preserved for reproducibility. Read `P3B_REVIEW_2026-10-28.md` and the latest
handoff section for final evidence; do not replay the historical restart
instructions as if P3-B were still open.

This is the latest execution contract, 28 October 2026. The user requests
resubmission with memory control and moving the project data to D:.

## Workspace and recovery

Actual project storage is now `D:\codex\pi-irrationality`.
The six content directories under the old C: project path are compatibility
junctions; the occupied C: root itself was retained. Full-copy path, size
and SHA-256 verification passed. Read `D_DRIVE_MIGRATION_2026-10-28.md`.
Do not delete the destination or its separate D: rollback archive.

Keep existing P1/P2/P3-A proofs and cache. P2-only historical launch text is
completed work. Current work is P3-B; do not repeat P2 validation as its result.
The original thread's persisted goal was blocked after restart; a new message
alone does not prove its lifecycle has resumed. Report the actual goal state.

## Mandatory compilation guard

From the workspace root, use only:

    python scripts/bounded_lean.py <project-relative-Lean-file> --timeout 180 --log logs/<unique-trial>.log

Example target path:

    OddPiPowers/Arithmetic/TwelveLayerCells.lean

The runner launches `lake env lean`, not a build graph, with one thread and
Lean's 2048 MiB memory limit. A Windows job object independently caps the
entire child process tree at 6144 MiB, kills remaining children on close,
prevents two guarded runs with a named mutex, and enforces a trial timeout.
It refuses launch below 2560 MiB free physical memory or 12288 MiB free commit,
and terminates its job if free physical memory falls below 512 MiB or free
commit below 2048 MiB. The hard-cap self-test has passed without running Lean.

During deployment a compiler-only check passed with about 1379 MiB peak job
commit. A minimal Mathlib import hit the preliminary 3072 MiB cap. The final
6144 MiB cap accounts for imported/mapped module data as well as Lean's
separately limited 2048 MiB computation memory. This adjustment was made during
deployment, before activating the goal; do not raise it further during proof
work. Refactor imports and proof batches if the final cap is insufficient.

Do not bypass the guard, change its caps, launch raw `lake build`/`lean`,
overlap compilation with generation, or leave a probe running and start a
replacement. If a small proof exceeds a limit, split or simplify the proof
representation. Do not re-run the same expensive whole-table reduction.

The guard checks one file; add `--emit` only when its compiled .olean artifact
is needed. Output stays inside the project's `.lake/build/lib/lean` tree.
It refuses to start while another Lean/Lake process already exists.
All later build/audit commands must also remain within equivalent hard caps;
do not remove the guard merely to perform final validation.

For final Lake validation use the same runner with `--build-target
OddPiPowers` (or one project module target), never raw Lake. The library's
`moreLeanArgs` must preserve one thread and 2048 MiB. The job also permits at
most two child processes: direct pinned-toolchain Lake and one child. The
runner selects the installed direct Git binary for metadata checks, avoiding
launcher processes. If Lake tries to overlap workers, the extra process is
refused; serialize targets with `scripts/guarded_library_build.py`
instead of increasing that limit. All aggregate memory and timeout caps stay
unchanged.

## Exact mathematical restart point

The rewrite errors in `TwelveLayerCost.lean` have been repaired in the
preceding run; its current dependency chain is still unaccepted.
`TwelveLayerCells.lean` now contains the unfinished adjacent-order/per-row
kernel proof refactor. Preserve the table, chunk data and all partial lemmas.
The earlier claims about 30 native-evaluation proofs are historical; inspect
the active source. Old table builds are not evidence that the new source
compiles or has acceptable transitive axioms.

First close **one** small certificate row with ordinary kernel-checkable
arithmetic, measuring cost through the guard. Then establish a reusable
soundness lemma and scale by small separately compiled modules, rather than
large reductions of nested whole-table expressions. Do not replace the full
twelve-layer certificate by zero bounds, a single interval or samples.

Finish the all-real certificate lower function, weight scaling, actual
carryWeightMinimum/common-divisor applications and the continuous p=41
example as specified in `P3B_CELL_CERTIFICATE_GOAL.md`. Root integration,
complete guarded validation and an executed final transitive axiom audit
remain required before P3-B acceptance. No sorry, project mathematical axiom,
or native-evaluation axiom is permitted in the final dependency closure.

## Stopping boundary

Stop at accepted P3-B. Do not expand to PNT/gamma, full contour estimates or
final numerical bounds. Do not claim completion because the old 131-entry
root audit passes. If the same external workspace-routing blocker repeats,
report it without launching compiler work or repeatedly revalidating P2.

Do not create another thread, change the model, set a token budget, modify
system paging settings, or migrate other projects as part of this goal.
