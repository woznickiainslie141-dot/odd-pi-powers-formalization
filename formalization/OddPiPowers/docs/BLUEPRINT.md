# Blueprint and correspondence

Complete P6 is accepted: actual scaled twelve-layer quotient rows, uniform
heights and remainders, finite certified gamma, exact analytic constants and
the unconditional exponent 42170551935/35026168 <1203.973. The complete root
and exact 424-new/602-regression axiom audits passed. Read
formalization/P6_REVIEW_2026-10-30.md and P6_CURRENT_CHECKPOINT.md first.
P7 applications require a later assignment; earlier status entries below
are historical.

P6-B current milestone: actual balanced AuxiliaryFamily and the unconditional
ExponentUpperBound(pi^3,14819/2) are accepted. Full <1203.973 P6 remains active.
Current checkpoint: formalization/P6_CURRENT_CHECKPOINT.md, workspace-relative.

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

Status labels: **proved** means a named Lean declaration builds and has been
checked for its axioms; **open** means no such declaration is available. A
manuscript argument is not itself a Lean proof.

| Paper | Required statement / module | Status |
|---|---|---|
| §1 | Irrationality-exponent interface and `LiouvilleWith` equivalence (`ExponentUpperBound.lean`) | proved; includes irrationality and all unreduced fractions |
| §5 | `coefficientPolynomial_eval_sub`, `polynomial_eval_sub` (`Transfer/DividedDifference.lean`) | proved; no additional hypotheses |
| §5 | `gaussian_norm_ge_one` (`Foundations/GaussianArithmetic.lean`) | proved; nonzero Gaussian integer |
| §5 | `exists_nonzero_row` (`Transfer/NonzeroRow.lean`) | proved; coefficient matrix determinant nonzero |
| §5 | `primitiveNormalization_dvd_of_fraction_dvd` (`Transfer/PrimitiveNormalization.lean`) | proved over any fraction field of a normalized GCD domain |
| §5 | `primitive_minpoly_dvd`, `primitive_minpoly_associated`, `primitive_minpoly_resultant_ne_zero` (`Transfer/MinimalPolynomial.lean`, `Transfer/MinimalResultant.lean`) | proved for an integral element over the fraction field |
| §5 | `gaussian_algebraic_value_lower_bound` (`Transfer/AlgebraicValue.lean`) | proved assuming a nonzero annihilator, its degree and leading-coefficient bounds, and uniform bounds on its roots and on `U` |
| §5 | `gaussian_binomial_value_lower_bound` (`Transfer/Binomial.lean`) | proved for any binomial with nonzero leading coefficient and a selected root in the disk |
| §5 | `irrationality_transfer`: uniform transfer, rounded multiples of L, root comparison and epsilon closure | proved, conditional on the explicit `AuxiliaryFamily` to be constructed |
| §2 | Reciprocal series, signed bounded distances/lcm, offsets and local product denominator budget (`LocalDenominators.lean`) | proved; applied to actual finite interval coefficients in P2 |
| §2 | Finite coefficient family, supports and high-order vanishing (`ActualAuxiliary.lean`) | proved in P2 |
| §2 | Unit-weighted jets, actual leading-block identification, full determinant identity and nonsingularity at i | proved in P2 |
| §3 | Signed-floor and zero-safe valuation estimates, actual coefficient divisor and integer quotient determinant (`Arithmetic/`) | proved in P3-A; 131-entry integration audit |
| §3, §7 | Continuous-cell/endpoint soundness, 1180-row twelve-layer certificate, two-layer certificate, scaling and actual divisor bridge | proved and P3-B accepted; all 72 project build targets and fresh 172-entry post-build audit passed |
| §3 | Prime-number input, psi/log-lcm and finite-window actual-divisor rates | proved; P4 accepted, 104-module validation and 67+172 audit checks |
| §4 | Whole-line paired-factor inequality and exact complex norm-square ratio (`HorizontalPair.lean`) | hard kernel proved |
| §4 | Actual full finite-product horizontal tail, both-line nonvanishing, global integrable majorant and uniform 17-row-family domination | proved; P5-A accepted, 111-module validation and 55+239 audits |
| §2, §4 | Actual finite pole-circle representation at i, weighted horizontal kernels and fixed-scale vertical-side vanishing; all 17 actual rows | proved; P5-B accepted, 122-module validation and 78+294 audits |
| §4 | Actual rectangle/circle comparison, full lower-minus-upper horizontal representation, Jacobian n and all 17 rows | proved; P5-C accepted, 132-module validation and 57+372 audits |
| §4 | Uniform coefficient height | open |
| §4 | Actual central Stirling/Riemann rate and uniform row remainder exponent | proved; P5-E accepted |
| P6 | Rational rate-certificate soundness with explicit AuxiliaryFamily input | proved; bounded P6-A accepted, full numerical instance open |
| §6 | Every fixed odd k: explicit scale and positive gap | open |
| §6–7 | Four strict rational numerical comparisons | open |

Dependency order is P0 → P1 → P2 → P3 → P4/P5 → P6 → P7.
The proved transfer statement quantifies fixed `k ≥ 2`, `m ≥ 1`, `L ≥ 1`,
`G ≥ 0`, and `D - (k-1) G > 0`. It will assume Gaussian-integer
polynomials of degree at most `m`, invertible coefficient matrices for every
positive `n = L*r`, and, for every positive `η`, a single threshold applying
to every row and every point in the radius-2 disk. It must derive the usual
irrationality-exponent assertion with exponent `m*(D+G)/(D-(k-1)*G)`.
The divided difference is a complex polynomial, not a Gaussian-integer one.
The minimal-polynomial resultant and row-selection facts are proved dependencies,
not fields of this input. See `LUNA_HANDOFF.md` for the remaining construction
bridges and the narrowed goal's final verification record.
