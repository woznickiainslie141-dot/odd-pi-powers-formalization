# Trust boundary

## Current P5-E and P6-A acceptance

P1 through P5-D and P5-E are accepted. The actual central Stirling/Riemann
rate is now proved, including endpoints, common normalization and uniform
actual/reduced-row exponential bounds for every fixed Y>1/2. The seventeen
base rows are instantiated. Generic fixed integer endpoint families are
also covered. P6-A rational certificate soundness is accepted, retaining
the full AuxiliaryFamily explicitly as a hypothesis.

Complete validation: 151 modules, 3 executed
targets and 148 verified records, fresh complete
root (4010 jobs), 50 new and 471 prior axiom checks. Only propext,
Classical.choice and Quot.sound occur. Fresh audit peak 5144.55 MiB under
the unchanged 6144 MiB cap. All 139 prior mathematical sources are unchanged.
See formalization/P5E_REVIEW_2026-10-29.md and
formalization/P5E_CURRENT_CHECKPOINT.md (workspace-relative paths).

P6 is not numerically closed. For the fastest first closed instance, use
the balanced all-pole family, unreduced coefficients and a fixed rational
height; its height proof avoids regular factors and improved gamma.
For the manuscript target: explicit s=11, M=187 actual family and
grouping for the pi^3 target; uniform coefficient heights and disk/difference
bounds; complete actual AuxiliaryFamily; sharp divisor rate and kernel-checked
pi/log/atan numeric certificates. The exact height APIs are recorded in
formalization/P5_HEIGHT_PROOF_PLAN.md. Optimal-height existence/uniqueness
is not a prerequisite.

Earlier stage records below are historical; their older open lists do not override this checkpoint.

## Historical P5-D acceptance

P1 through P5-C and P5-D are accepted. The explicit actual central remainder
bound is uniform in row and scale, connected to the actual Gaussian quotient,
and instantiated for all seventeen base rows. Exact finite center logarithms,
the single-interval integral and its height derivatives are proved.
Complete validation: 140 modules (8 executed,
132 verified records, including 131 prior unchanged
modules), fresh full root (3999 jobs), 42 new and 429
prior axiom checks. Only propext, Classical.choice and Quot.sound occur.
Peak fresh audit 5139.93 MiB under the unchanged 6144 MiB cap.
See ../P5D_REVIEW_2026-10-29.md and ../P5D_CURRENT_CHECKPOINT.md.

The bounded goal is complete. Coefficient heights, central Stirling/Riemann
rates, optimal-height theorem, sharp gamma, general odd-power parameters and
final numerical exponents remain open. No complete AuxFamily is claimed.

The following earlier stage records retain their historical scope.

The intended results must follow from Lean's kernel and the usual foundational
axioms reported by `#print axioms`. Project-specific mathematical axioms,
`sorry`, `admit`, external Arb outputs, and unproved analytical hypotheses are
not acceptable in the dependency closure of a final result.

Mathlib is a pinned source dependency. P4 accepts the required 19-module
proof subset of PrimeNumberTheoremAnd at the recorded revision. The unused
unfinished branch is omitted, with source provenance and license preserved.
The compiled PNT declarations and their project applications passed executed
transitive axiom checks. The full upstream package is not a dependency.

Certificate JSON and Python/Arb output supply candidate values only. Their
contents have no proof status in this project.

The earlier P1 declarations were checked in `logs/p1-axioms.log`. P1 is now
closed: `logs/hard-core-p1-axioms.log` includes `irrationality_transfer` and
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The narrowed hard-kernel checkpoint extends `AxiomAudit.lean` to the repeated-node,
denominator and horizontal-pair modules. Its final output is
`logs/hard-core-final-axioms.log`; use its successful exit and actual dependency
sets, not the mere existence of the audit file, as verification evidence.

The final audit completed with exit code 0: 85 declarations, with the union of
axioms exactly `propext`, `Classical.choice`, and `Quot.sound`. The final full
library build also completed with exit code 0 and no warnings. This verifies
the hard-kernel checkpoint, not the unconstructed concrete auxiliary family.

The abstract transfer theorem still requires the concrete `AuxiliaryFamily`.
No final theorem instantiating it with the nested construction or numerical
parameters exists. A clean abstract theorem and kernel lemmas are not a proof
of the advertised numerical pi-power bounds.

P3-A integration acceptance, 27 October 2026: all five arithmetic modules are
imported by the root, and the complete build passed with 3116 jobs
(`logs/p3-integration-review-build.log`). The executed `AxiomAudit.lean`
contains 131 checks and exited 0; its reported axiom union is exactly
`propext`, `Classical.choice`, `Quot.sound`
(`logs/p3-integration-review-axioms.log`). This accepts the actual arithmetic
divisor and quotient construction. It does not accept continuous certificate
JSON, prime asymptotics, or the final numerical bounds.

P3-B proof/audit checkpoint, 28 October 2026: the updated root compiles under
the memory guard, and the executed audit covers 172 distinct declarations
(`logs/p3b-final-axiom-audit.log`). Its axiom union is exactly propext,
Classical.choice and Quot.sound; no sorryAx or native-evaluation axiom is
present. This includes the actual all-real lower bound and scaled integer
coefficient divisibility, not merely a generic checker or external data.
The complete 72-target serial Lake validation passed with exit 0, and the
fresh post-build audit (`logs/p3b-post-build-axioms.log`) again passed all
172 distinct checks with exactly the same usual axiom union. The build
manifest's source hashes match the current files. P3-B is accepted; see
`../P3B_CURRENT_CHECKPOINT.md` and `../P3B_REVIEW_2026-10-28.md`.


## P4 final acceptance and P5-A handoff — 29 October 2026

P4 is accepted. Complete dependency validation covers 104 current modules;
the final run executed 25 targets, reused 79 source-identical verified records,
and built the full root afresh (3963 jobs). Fresh audits cover exactly 67 new
checks and 172 regression checks, with only propext, Classical.choice and
Quot.sound. Peak final build 3556.75 MiB; peak audit 5105.83 MiB, below 6144.
See ../P4_REVIEW_2026-10-28.md and logs/p4-acceptance-2026-10-28.json.

The concrete actual divisor has rate 2/69 with arbitrary positive slack;
the general finite-window and scaled-grouping interfaces are proved. Sharp
gamma evaluation and final numerical pi-power bounds are not established.

P5-A is newly authorized: ../P5A_HORIZONTAL_GOAL.md. Work on actual finite
denominator products and whole-line integrability. Preserve P1–P4 acceptance,
toolchain, manifest, caches and the unchanged single-compiler memory guard.
Do not repeat accepted P2/PNT checks or revive the obsolete blocked thread.


## P5-A final acceptance — 29 October 2026

The assigned P5-A goal is complete. See ../P5A_REVIEW_2026-10-29.md,
../P5A_MATHEMATICAL_NOTES.md and logs/p5a-acceptance-2026-10-29.json.
The complete 111-module dependency validation passed with 8 executed targets,
103 unchanged verified P4 records and a fresh full root (3970 jobs).
Fresh audits passed exactly 55 new declarations and 239 regression checks;
their axiom union is propext, Classical.choice and Quot.sound. Peak new build
3288.35 MiB, peak audit 5126.0 MiB, below the unchanged
6144 MiB job cap. No parallel proof, paging change or cache clearing occurred.

Seven new Analysis modules connect the actual denominator polynomial to the
reflection product, prove nonvanishing and squared norm lower bounds on both
horizontal lines, prove explicit Cauchy domination and integrability, and
bound the actual rational kernel and its integral. The normalized kernel
has a common integrable majorant for all h<=m and d>=2(m+2). The actual
17-row family meets the threshold for every positive N, so its same majorant
is uniform in N, row and line. All 103 old mathematical source hashes and
the saved accepted P4 root match their ledger; manifest/toolchain unchanged.

The next substantive gap is the fixed-n contour/residue representation,
including branches/exponential factor, vertical sides and exact connection
to actual polynomial coefficients. Height and central asymptotics, sharp
gamma and final numerical bounds are also open. P5-A does not accept them.
Do not resume the obsolete blocked task or rerun accepted P2/PNT work.


## P5-B final acceptance — 29 October 2026

The assigned P5-B goal is complete. See ../P5B_REVIEW_2026-10-29.md,
../P5B_MATHEMATICAL_NOTES.md and logs/p5b-acceptance-2026-10-29.json.
Complete dependency validation covers 122 modules, 12 executed targets,
110 verified unchanged P5-A records and a fresh full root (3981 jobs).
Fresh audits passed exactly 78 new and 294 prior declarations, with only
propext, Classical.choice and Quot.sound. Peak new build 3292.19 MiB;
peak audit 5130.09 MiB under the unchanged 6144 MiB cap. All 110 prior
mathematical source hashes and the saved P5-A root match the accepted ledger.
Toolchain v4.35.0 and manifest remain unchanged.

Eleven new Analysis modules prove actual partial fractions and genuine small
pole-circle integrals, exact actual row normalization at i, both-line
exponential horizontal integrability and both fixed-scale vertical limits
for the full factorial kernel. The actual 17-row family is instantiated.
The independent helper conversation drafted only ContourExponential and
ActualRemainderAlgebra and ran no compiler/generator. Main repaired, checked,
integrated and audited all results. The helper is idle; compiler access
remains exclusively with main under the existing bounded runner.

Next hard bridge: an explicit comparison of the pole-circle contour with a
large rectangle, then horizontal truncation limits. Existing weighted
integrability and vertical limits do not imply that equality by themselves.
After that, coefficient heights and central rates are still required before
the auxiliary family can instantiate the transfer theorem. Sharp gamma and
final numerical pi-power bounds remain open. Do not revive obsolete tasks,
replay P2/PNT checks or weaken the resource guard.


## P5-C final acceptance — 29 October 2026

The assigned P5-C goal is complete. See ../P5C_REVIEW_2026-10-29.md,
../P5C_MATHEMATICAL_NOTES.md and logs/p5c-acceptance-2026-10-29.json.
Complete dependency validation: 132 modules, 11 executed targets,
121 unchanged verified P5-B records and a fresh full root (3991 jobs).
Fresh audits passed exactly 57 new and 372 prior checks, with only propext,
Classical.choice and Quot.sound. Peak new build 3294.46 MiB;
peak audit 5135.56 MiB, below the unchanged 6144 MiB cap. All 121 prior
mathematical sources and the saved P5-B root match accepted hashes; toolchain
v4.35.0, manifest, vendor provenance and caches are preserved.

Ten new Analysis modules close actual finite rectangle/circle comparison
and full lower-minus-upper horizontal representation. The proof uses exact
logarithm jumps, higher-power primitives and entire dslope induction, then
actual finite principal parts. The Jacobian n and fixed-scale limit order
are proved, with exact actual row-at-i and norm formulas and all seventeen
base-family rows instantiated. No unproved contour equality is an input.

The independent helper drafted only HorizontalLineLimits and its handoff,
without running a compiler or generator. Main repaired, checked, integrated
and audited the draft and all core work. Compiler access stays with main.

Remaining work: uniform coefficient heights and central Stirling/Riemann
exponential rates, sharp gamma arithmetic, explicit scaled families and
general odd-power parameter/numerical closure. P5-C does not accept those
results or the final irrationality bounds. Do not repeat P2/PNT validation,
revive obsolete tasks or weaken the resource guard.
