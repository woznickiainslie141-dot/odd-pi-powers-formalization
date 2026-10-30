# D-drive relocation and bounded-memory restart — 28 October 2026

## Completed storage migration

Actual working data: `D:\codex\pi-irrationality`.

The source project had 59,067 files, totaling 4,308,829,035 bytes. Before
switching, every relative file path, size and SHA-256 hash matched the D copy.
Verification record: `D:\codex\pi-irrationality-migration-verified.json`.

Codex held the old C root directory open, preventing a root-directory rename.
The existing C root was retained, and each of its six content directories
was replaced by a verified junction to the corresponding D directory:
`formalization`, `logs`, `output`, `research`, `scripts`, and `tmp`.
Critical files are readable through both paths and their hashes match.
The small root `AGENTS.md` exists at both roots with identical instructions.

The original C data was preserved as a separate rollback archive at
`D:\codex\.c-migration-originals-20261028`. Its complete original inventory
was checked: 59,067 files and 4,308,829,035 bytes. The first incomplete move
left 15 files in `D:\codex\pi-irrationality-originals-20261028`; they were
copied back into the full rollback archive without conflicts. That small
partial directory is retained, not part of the working project.

Automatic review blocked recursive deletion of the verified C duplicate.
The safer completed action moved all originals to D, retaining their data.
The C duplicate directory no longer exists. C free space increased from
approximately 7.55 GiB to 11.51 GiB; D has approximately 12.12 GiB free after
retaining both the working copy and full rollback copy. Exact free space is
dynamic. Do not delete the compatibility junction paths recursively.

## Paging-file observation

Observed configuration:

- Automatic management is off.
- C: initial 24 GiB, configured maximum 28 GiB; current allocation 24 GiB.
- D: configured initial 48 GiB, maximum 64 GiB, but not reported as an active
  paging file by Win32_PageFileUsage; its file was not found in this check.
- D had only about 20.4 GiB free even before migration, below that configured
  48 GiB initial size. No assumption is made that this setting is effective.

No paging, registry or system settings were changed. Relocating data frees C
space but does not itself increase a configured commit limit. This restart
therefore also enforces compilation memory limits.

## Tested resource control

`scripts/bounded_lean.py` launches one Lean source check under a Windows job
object with a final 6144 MiB aggregate child-process-tree commit limit and
kill-on-close. Lean is separately given 2048 MiB and one thread. A named
mutex prevents overlapping guarded trials; the runner also refuses launch
while another Lean/Lake process exists. Trial timeout and system low-water
checks terminate only the runner's own job.

The hard-cap self-test passed both before and after relocation: a 96 MiB
allocation was rejected under a 48 MiB job cap. No proof was trusted on the
strength of that test. The preliminary 3072 MiB cap was too tight even for
a minimal Mathlib import; it rejected the allocation and the system remained
stable. A compiler-only check passed with about 1379 MiB peak job commit.
With the final 6144 MiB job cap, the minimal Mathlib check passed with exit 0
and about 3127 MiB peak job commit; see
`OddPiPowers/logs/d-drive-mathlib-smoke-final.log` and its `.job.json` metrics.
The final guard requires at least 12288 MiB free system commit before launch.
Its Lean-internal cap remains 2048 MiB, with one worker. No further limit
increase is authorized for the proof-work goal.

The first `SignedCarry.lean` smoke attempt failed while loading its heavy
`ActualAuxiliary` dependency under the preliminary cap. The reported private
object exists and has an identical SHA-256 hash to the original backup;
there is no observed file corruption. Do not reinstall the toolchain based
on that resource-constrained read error.

## New goal location

The old task remains blocked after `workspace routing discovery failed` and
must not be revived in parallel. The user authorized resubmission; the
new goal was created and read back as **active** in the current chat
(`01a17713-f07e-7ae3-b4fd-8cec070858ee`), with no model or token-budget
override. Its contract is `P3B_MEMORY_BOUNDED_GOAL.md` and the root
`AGENTS.md`. Preserve current mathematical work and finish P3-B before any
P4/P5/numerical expansion.
