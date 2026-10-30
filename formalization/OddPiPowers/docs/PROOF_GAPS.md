# Proof audit and open bridges

Complete P6 is accepted on 30 October 2026. The actual s=11 family,
general heights, central rates, sharp finite divisor certificate and fixed
numeric transfer close the target below1203.973. No P6 bridge remains.
The exact theorem, root/source verification and 424+602 axiom audit evidence
are in formalization/P6_REVIEW_2026-10-30.md and the accepted JSON report.
General odd-power applications and other manuscript examples remain P7.
The P6-B and earlier open-gap descriptions below retain historical scope.

Current P6-B milestone: the complete balanced actual family and the
unconditional pi^3 bound7409.5 are accepted (164 modules,81+521 audits).
The uniform balanced height gap is closed. The full <1203.973 P6 goal is
active; general interval heights, s=11 family/grouping, sharp gamma and
refined numeric certificates remain. The direct general-factor route is in
formalization/P6_GENERAL_HEIGHT_SIMPLIFICATION.md and supersedes the earlier
requirement to prove a regular-factor product identity for height alone.
Earlier stage summaries below are historical.

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

The following are obligations identified in the manuscript, not claims that
the stated mathematical results are false. Updated after the hard-kernel work:
P1 is closed, and parts of the algebraic and local denominator obligations are
now covered by general Lean theorems. See `LUNA_HANDOFF.md` for precise APIs.
P1 through P5-B and P5-C are accepted. Complete dependency validation covers
132 modules and fresh audits of 57 new plus 372 prior checks, with only
propext, Classical.choice and Quot.sound. See ../P5C_REVIEW_2026-10-29.md.
The actual finite-to-infinite contour bridge is closed; the whole original
irrationality-measure formalization remains incomplete.

1. **§5, algebraic value.** The full binomial can share a root with `U` even
   when `U(y) ≠ 0`; §8 gives an explicit example. Use a primitive polynomial
   derived from the actual minimal polynomial, descend divisibility through
   Gauss's lemma, bound its leading coefficient, and prove its resultant is
   nonzero. Include multiplicities and degree-zero edge cases. **Discharged
   in P1**, through `irrationality_transfer` and its dependencies.
2. **§2, determinant. Discharged for P2.** In
   `Construction/ActualAuxiliary.lean`, support and degree bounds, the
   prescribed leading-column local jets, the exact repeated-block/jet-order
   bijection, and the nonzero local-unit constants are proved. The leading
   matrix is explicitly converted to unit-weighted jets and
   `eq_zero_of_unit_weighted_jets` proves its determinant nonzero. The
   exponential determinant divisibility is transferred to the polynomial
   determinant at `1`; after removing the support factor, the degree bound
   gives the complete factorization

       det A(X) = det(leading matrix) * X^(sum left endpoints)
                    * (X - 1)^(sum interval lengths).

   Mapping this identity to `ℂ` at `Complex.I` proves `det A(i) ≠ 0` for the
   actual evaluated matrix. The all-pole partial-fraction identity was not needed by P2; P5-B now
   proves its actual meromorphic evaluation and uses it to derive the finite
   pole-circle integral representation. The separate `confluentMatrix_det_ne_zero` theorem
   remains available as a generic kernel.
3. **§2–3, local factors.** The actual construction now proves the pole
   binomial/factorial identity, clears the regular finite partial fractions
   to the interval factorial, and identifies both pole and regular local
   factors after multiplication by their local denominators. It applies the
   existing LocalDenominators kernel to obtain coefficient integrality and
   an explicit integer-polynomial lift. **Prime valuations and the actual
   common divisor are discharged in P3-A.** The five arithmetic modules
   prove the signed-carry local estimates, actual coefficient divisibility,
   finite-pole-minimum divisor, and integer quotient determinant. Continuous certificates were subsequently accepted in P3-B and finite-window
   divisor rates in P4; sharp arithmetic gamma remains separate.
4. **§3, cell certificate.** Midpoint evaluations alone do not prove all
   continuous cells and endpoints; verify order stability, circle wraparound,
   repeated endpoints and the weakened zero value at critical z.
   **Discharged at the theorem level in P3-B:** 1180 exact rows, endpoint/gap
   soundness, ordered open cells, periodized lower bound, boundary-zero values,
   weight scaling and actual `carryWeightMinimum`/coefficient divisibility are
   built and included in the successful 172-entry root audit. The two-layer
   and continuous p=41 instances are also included. **P3-B accepted:** all
   72 serial Lake build targets and the fresh 172-entry post-build audit
   passed; current source hashes match the complete build manifest.
5. **§3–4, limits. P4 arithmetic rate discharged.** Fixed finite interior
   windows give unconditional eventual actual-divisor rates. The theta/psi
   proof closure and all project bridges passed final build and axiom checks.
   The concrete rate 2/69 is only a calibration; sharp gamma remains open. Open the contour for fixed n,
   take horizontal truncation to infinity, then take n to infinity; supply an
   integrable bound over the entire line and estimates uniform in rows.
   **Pair algebra discharged:** `horizontal_pair_tail`, with its exact complex
   norm-square ratio. **P5-A discharged:** actual denominator finite products, exact degree,
   both-line nonvanishing, global integrable majorant and actual kernel
   integrability, with scale/row-uniform concrete 17-row-family domination.
   **P5-B discharged:** actual finite pole-circle representation at i,
   exponential-weighted horizontal integrability and both fixed-scale vertical
   limits, including the actual 17-row family. **P5-C discharged:** finite rectangle/circle comparison and the actual
   infinite horizontal representation, with correct orientation, normalization
   and Jacobian n, including all seventeen actual rows. Coefficient heights
   and central asymptotics remain open.
6. **§5, quantifiers.** The selected row may depend on p, q and n. Bounds and
   thresholds must be uniform in the entire disk and all rows. Make the ceiling
   and epsilon choices explicit and cover unreduced fractions as well.
   **Discharged in P1**, including the epsilon closure.
7. **§6–7, numerical route.** The provided root-free certificate for k=3,
   s=11 gives approximately 1203.98515, above 1203.973. Thus that weaker
   estimate alone cannot prove the requested cubic target. A fixed rational
   height sufficiently close to the optimized one, with independently proved
   interval estimates, is needed. Arb values are candidate data only.

No manuscript source has been modified. No listed open gap has been certified
as a counterexample to the original claim; each is a required explicit proof
or bridge for the broader formalization. P2's actual determinant application
is closed; the original full result remains unverified.
