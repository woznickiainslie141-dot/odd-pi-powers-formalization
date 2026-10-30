# Current goal: finish P3-B, not another P2 review

## Memory exhaustion supersedes the older pause checkpoint

Read `RECOVERY_AFTER_MEMORY_EXHAUSTION_2026-10-28.md` first. Windows confirmed
virtual-memory exhaustion at 01:12; the reboot was followed by a workspace
routing failure, and the persistent goal is now blocked. Do not immediately
resume a whole-table build. Preserve the current per-row/adjacent-order proof
refactor and start with a single process, a small proof block and an explicit
memory limit after routing is restored. The previously built full table is
not current acceptance evidence after these source changes.

## 28 October pause diagnosis — read first

See `P3B_PAUSE_DIAGNOSIS_2026-10-28.md`. The persistent goal remained paused
despite the last continuation message; use the actual goal resume control.
The last compaction dropped the newer P3-B message and retained the old
P2-only request. A normal running turn does not establish an active goal.

Preserve the newly built `Arithmetic/TwelveLayerCellData.lean` and
`Arithmetic/TwelveLayerCells.lean` table/validity modules. The last run checked
1180 cells in 30 blocks. Continue from `Arithmetic/TwelveLayerCost.lean`,
whose all-real correctness proof is the current unaccepted bridge; do not
regenerate or reprove the table by default. The older execution-order section
below predates these additional modules.

## Latest authorization and state

The user has authorized continuing and deploying the next step. This resumes
the paused P3-B goal. Earlier P2-only startup instructions describe an accepted
checkpoint and do not delimit this continuation. Preserve P1, P2 and P3-A.

The previous run implemented partial P3-B source, then returned to a P2-only
review and paused P3-B. Consequently P3-B has NOT passed acceptance. The
131-entry root audit does not cover the new continuous modules. Do not treat
that successful audit as P3-B completion, and do not spend another run merely
revalidating P2.

Independent resumption check: both named modules now pass a targeted build
with 2166 jobs, exit 0 (`OddPiPowers/logs/p3b-resume-review-build.log`). This
confirms their compilation, not full P3-B acceptance. No mathematical source
was changed during this resumption review. Their additional axiom audit and
root integration remain part of the current task.

The full specification remains `P3B_CELL_CERTIFICATE_GOAL.md`. This file fixes
the current execution order and recovery scope. Read this file again after
context compaction, together with the latest user instruction.

## Execution order

1. Resume the existing P3-B goal, retaining its correct completion conditions.
   Inspect `OddPiPowers/Arithmetic/ContinuousCarry.lean` and
   `OddPiPowers/Arithmetic/CertifiedPrimeDivisor.lean` before writing duplicate
   code. The former already contains periodicity, boundary-indicator formulas,
   weight scaling and twelve positive two-layer intervals. The latter contains
   the actual grouping, divisor bridge and continuous 41-divisibility example.
2. Compile both named modules. Fix actual errors if present. This partial
   checkpoint must include the all-real two-layer bound and its connection to
   the actual coefficients, not just finite pole enumeration. Do not stop here.
3. Build the finite rational certificate checker and complete the twelve-layer
   L=69, offsets 0,...,11, base weights (6,1,...,1) configuration. Use the exact
   candidate data and endpoint geometry in the full specification. Do not
   replace it with a single positive interval, a few samples, or zero bounds.
4. Reuse scaling to obtain all positive integer multiples of the base weights.
   Connect the certified lower function to `carryWeightMinimum` and the actual
   coefficient divisor through the existing grouped bridge.
5. Import all final modules from the root and add their key final declarations
   to `AxiomAudit.lean`. Run a complete build and execute the transitive axiom
   audit. Update status, gaps, blueprint and handoff consistently. Only then
   mark P3-B complete and stop for acceptance.

The checker must cover all real z,y, including all y endpoints and coincident
branches; set the lower function to zero at the fine z-cell boundaries. A
merged candidate interval can contain changes of endpoint order. Checking
its midpoint alone is invalid. Candidate generation may use Python fractions;
soundness and acceptance must be Lean-kernel verified. No new mathematical
axioms, sorry, or native-evaluation axioms.

## Resource and scope control

Use the pinned Lean/Mathlib v4.35.0, existing manifest and selective imports.
Use two workers where needed; do not clear `.lake` or reinstall the toolchain.
Keep concise logs and inspect error contexts instead of dumping full traces.

No new token budget or model override is requested. Do not start another
thread or delegate. No PNT/gamma, contour opening, Stirling, or final numerical
bounds belong to this P3-B goal. If a genuine obstruction remains, report the
smallest unclosed theorem and retain the accepted work; do not substitute a
completed P2 review for the current goal.

## Remaining route after P3-B

This is not the final stage of the original full goal:

- P4: an accepted prime-number input and a one-sided exponential lower rate
  for the certified divisor. A conditional PNT assumption is not completion.
- P5: finite-product bounds, full-line integrability, fixed-n contour opening,
  Stirling/rate estimates uniform in rows and in the required disk, then the
  actual `AuxiliaryFamily` instance. Only the paired-factor algebra is done.
- P6: kernel-verified numerical bounds, beginning with the cubic case. The
  weaker root-free estimate does not reach 1203.973; it needs a sufficiently
  sharp fixed rational height and proved inequalities.
- P7: the general odd-power parameter construction and the remaining explicit
  k=5,7,9 instances, followed by final theorem axiom audits.

Do not bundle these substantial mathematical bridges into an apparent final
cleanup step or give a completion percentage based on source-line counts.
