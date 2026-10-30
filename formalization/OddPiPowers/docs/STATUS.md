# Status — complete P6 accepted

P6 is accepted on 30 October 2026. The unconditional theorem
pi_cube_exponentUpperBound_42170551935_div_35026168 proves the exponent
bound 42170551935/35026168 <1203.973. Complete validation covers 264 project
modules, with exact 424 new and 602 regression axiom checks using only the
usual three foundational axioms. All 163 prior mathematical sources match.
See formalization/P6_REVIEW_2026-10-30.md and P6_CURRENT_CHECKPOINT.md.
General odd-power applications are later P7 work. The milestone notes below
are historical and must not be treated as unfinished P6 instructions.

## Historical P6-B milestone

P6-B is accepted: `pi_cube_exponentUpperBound_14819_div_two` proves the
unconditional bound mu(pi^3)<=7409.5<7500. Actual balanced coefficients,
uniform heights, small remainders, nonsingularity and the fixed numerical
certificate are all proved. Root validation covers 164 modules, with fresh
81 new/521 regression axiom checks using only the usual three axioms.
See formalization/P6B_REVIEW_2026-10-29.md (workspace-relative).

The full P6 goal below1203.973 remains active. General actual-factor height
and the s=11 reduced family, sharp gamma and refined numerical certificate
remain. Read formalization/P6_CURRENT_CHECKPOINT.md first for current work.

The stage records below retain their historical scope.

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

The original full goal is not complete. P1, P2 and P3-A are accepted.
The project data is now at `D:\codex\pi-irrationality`, with six compatibility
junctions under the old C: root. All 59,067 original files passed full path,
size and SHA-256 verification before switching. C free space increased to
about 11.5 GiB, with original data preserved in a separate D: rollback archive.
See `../D_DRIVE_MIGRATION_2026-10-28.md`.

The old task remains blocked after the restart's workspace-routing failure.
P3-B was resubmitted in the current chat and its persisted goal was verified
active, without a parallel old task.
Use `../P3B_MEMORY_BOUNDED_GOAL.md` and root `AGENTS.md`: one process tree,
6144 MiB hard job cap, Lean 2048 MiB internal cap, one worker, bounded trials
and system headroom checks. The hard-cap self-test and the D-drive minimal
Mathlib source check passed. All P3-B mathematical modules and the updated
root compile under the guard. The complete serial Lake build passed all
72 project targets; the final root reports 3156 build jobs. The fresh
post-build 172-entry audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. All source hashes match the completed build manifest.
P3-B is accepted; see `../P3B_REVIEW_2026-10-28.md`.

- P0: the pinned Lean/Mathlib v4.35.0 environment builds. Library source audit
  exists. The required pinned PNT proof subset is accepted after compilation and
  executed transitive axiom checks; the full upstream package is not imported.
- P1: complete. `irrationality_transfer` closes the abstract exponent theorem,
  including primitive minimal-polynomial descent, nonzero resultant, all
  rational fractions, root comparison, rounded multiples of L and epsilon
  closure. It assumes the explicit `AuxiliaryFamily`; its algebraic construction
  is now proved, while its uniform analytic bounds remain open.
- P2 hard kernels: repeated-node Taylor uniqueness, invariance under local unit
  power-series factors, and a concrete confluent matrix theorem are implemented.
  The local denominator calculus handles normalized reciprocals, raw regular
  reciprocals, integer-weighted sums, finite products, signed bounded distances
  and their lcm, and the multiplicity/order cancellation. See final verification
  in the handoff for their current acceptance record.
- P2 actual construction: complete for the requested checkpoint in
  `Construction/ActualAuxiliary.lean`. It includes the actual intervals,
  local expansions and partial-fraction coefficients; factorial/binomial
  identities; the direct `LocalDenominators` integrality argument and
  explicit lift to `Z[X]`; support and degree bounds; and the leading-column
  jet formula. The high-order zero at `1` is transferred from the exponential
  series determinant, and repeated-left-endpoint blocks are proved to index
  every jet order exactly once. The actual leading matrix is connected to
  `eq_zero_of_unit_weighted_jets`, proving its determinant nonzero. The full
  factorization
  `det A(X) = det(leading matrix) * X^(sum left) * (X-1)^(sum length)`
  and the nonzero determinant of the complex matrix `A(i)` are proved.
  The latest P2 revalidation passed the present library-root build with 3116
  jobs and no errors, and the executed 131-entry axiom audit;
  the P2 declarations are included.
  The current root already imports accepted P3-A arithmetic and the horizontal
  pair kernel. That historical P2-only run did not add P3-B to the root;
  the current P3-B integration and 172-entry audit now do.
  The latest rerun passed with 3116 build jobs and 131 audit checks. See
  `logs/p2-al-current-build-2026-10-28.log` and
  `logs/p2-al-final-2026-10-28-audit.log`.
- P3-A: complete. Five arithmetic modules prove signed carries, zero-safe
  local prime valuations, prime-power divisibility of the actual integer
  coefficients, a positive common divisor defined by finite-pole minima,
  and the integer quotient family with nonzero determinant at i. A genuine
  n=42, p=41 divisibility instance is proved. The modules are now imported by
  the library root and included in the audit. Independent integration build:
  3116 jobs, exit 0; audit: 131 declarations, exit 0, axiom union exactly
  `propext`, `Classical.choice`, `Quot.sound`. See
  `logs/p3-integration-review-build.log` and
  `logs/p3-integration-review-axioms.log`.
- P3-B: complete and accepted. All required mathematical statements compile,
  the complete engineering build passes, and the executed post-build
  transitive axiom audit passes. The two-layer
  full positive-cell bound, scaling and continuous 41-divisibility example
  are connected to the actual coefficients. The twelve-layer table has 1180
  individually kernel-proved rows in 30 modules, including 1166 positive rows.
  Adjacent endpoint checks imply ordered, internally disjoint open cells.
  `TwelveLayerCellSoundness` and `TwelveLayerCost` prove soundness for all real
  z,y including endpoint/gap cases. `TwelveLayerCertifiedBound` gives the
  periodized lower function, zero at all cell endpoints, scaling, and a
  nontrivial value at least 6. `TwelveLayerActualDivisor` connects it and all
  weight multiples to the actual finite-pole minimum and integer coefficients.
  Root compile: `logs/p3b-root-integration.log`, exit 0. Audit:
  `logs/p3b-final-axiom-audit.log`, 172 declarations, exit 0, usual axiom union.
  Serial Lake build: `logs/p3b-guarded-library-build-state.json`, completed
  with 72 exit-0 targets and matching current source hashes. Fresh final
  audit: `logs/p3b-post-build-axioms.log`, exit 0, 172 distinct declarations.
- P4: complete and accepted. Unconditional theta/psi limits, log-lcm rate 1,
  finite-window actual-divisor exponential lower bounds and scaling are proved.
  Concrete base-family calibration: 2/69. Sharp gamma arithmetic remains open.
- P5-A: complete and accepted. Actual denominator reflection, finite-product
  assembly, both-line nonvanishing, exact degree, whole-line majorant and
  actual kernel integrability are proved. The concrete 17-row family has
  uniform normalized domination for every N>=1. The fresh post-build checks
  cover all 55 new declarations; all 239 prior checks also pass.
- P5-B: complete and accepted. Actual finite pole-circle representation,
  weighted horizontal integrability, fixed-scale vertical sides and concrete
  17-row applications are proved; fresh 78-new/294-regression audits pass.
- P5-C: complete and accepted. Finite rectangle/circle comparison, exact
  infinite horizontal representation, Jacobian n and actual seventeen-row
  applications are proved; fresh 57-new/372-regression audits pass.
- Remaining P5: uniform coefficient heights and central Stirling/Riemann
  exponential rates remain open.
- P6–P7: none of the four numerical bounds or the general odd-power parameter
  application has been kernel verified. External Arb output is candidate data.

The P1 audit is `logs/hard-core-p1-axioms.log`. The narrowed-goal final audit
and build are recorded separately; consult the handoff's final record.

P5-C is closed. Remaining analytic rates and numerical/general odd-power
applications require a later assigned goal and further proof. Do not revive the blocked old task or describe the
remaining analytic/PNT obligations as routine arithmetic.
