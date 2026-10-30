# Luna max handoff: odd powers of pi

P6 is COMPLETE and accepted. Do not rerun its former open tasks. The fixed
unconditional exponent is 42170551935/35026168 <1203.973, with the actual
s=11/M=187 construction and exact numeric/divisor certificates. Full root
validation and 424+602 transitive axiom checks passed. Read
formalization/P6_CURRENT_CHECKPOINT.md and P6_REVIEW_2026-10-30.md for current
evidence. General actual-family interfaces are available for later P7 work,
which is not assigned by this completion. All compiler caps and main-only
ownership persist. The instructions below are historical records.

Current full P6 goal is ACTIVE. P6-B's unconditional balanced pi^3 bound
14819/2 is accepted; do not rerun that milestone as unfinished work.
Read formalization/P6B_REVIEW_2026-10-29.md and P6_CURRENT_CHECKPOINT.md
before the historical entries below. General actual factors now have a
direct polynomial-loss height route; the earlier regular product-identity
requirement was unnecessarily strong. All compiler ownership/caps persist.

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

This handoff is for continuing a partially formalized mathematical construction. It does not assert that any of the four numerical irrationality bounds has already been proved in Lean.

## 1. Project and scope

Work in `formalization/OddPiPowers/` under the current workspace. Lean and Mathlib are pinned to v4.35.0; preserve `lean-toolchain` and `lake-manifest.json`. Do not reinstall the toolchain or update Mathlib as a routine first step.

Read these documents in order:

1. This handoff.
2. `docs/STATUS.md` and `docs/PROOF_GAPS.md`.
3. `../HARD_CORE_GOAL.md` for the narrowed completed-work boundary.
4. `../FORMALIZATION_GOAL.md` for the original complete research target.

The manuscript is in `../../output/pdf/odd_pi_powers_notes/`; use sections 02–07 for the construction, arithmetic, analysis, transfer, parameters and numerical certification. The manuscript is a mathematical source to audit, not a trusted Lean dependency.

## 2. The abstract transfer theorem

Entry point: `OddPiPowers.irrationality_transfer` in `Transfer/IrrationalityTransfer.lean`.

Given `AuxiliaryFamily m L D G U`, `m ≥ 1`, `L > 0`, `k ≥ 2`, `G ≥ 0`, and

    D - (k-1)*G > 0,

it proves

    ExponentUpperBound (pi^k) (m*(D+G)/(D-(k-1)*G)).

`AuxiliaryFamily` is a genuine remaining construction obligation: integer-Gaussian polynomials of bounded degree, nonsingular coefficient matrix, and estimates uniform in every row and the entire closed disk of radius 2. The main theorem already proves the minimal-polynomial resultant, root comparison, rounded multiple-of-L selection, and epsilon closure. Do not assume binomial irreducibility; the proof correctly uses the actual minimal polynomial.

`Foundations/ExponentUpperBound.lean` connects the eventual all-fractions lower bound to irrationality and `LiouvilleWith`. The theorem includes unreduced fractions, so no gcd bookkeeping is necessary at the final transfer step.

## 3. Repeated-node kernel

File: `Construction/ConfluentJets.lean`.

Main interfaces:

- `pow_X_sub_C_dvd_iff_taylor`: vanishing Taylor coefficients below r are equivalent to divisibility by `(X-C a)^r`.
- `eq_zero_of_confluent_jets`: a polynomial of degree less than the sum of multiplicities, with the required jets zero at distinct nodes, is zero.
- `unit_mul_jets_iff`: multiplying by any power series with nonzero constant coefficient preserves vanishing of the first r coefficients.
- `eq_zero_of_unit_weighted_jets`: the same uniqueness statement with a different local unit series at each node.
- `confluentMatrix`, `confluentMatrix_mulVec`, `confluentMatrix_det_ne_zero`: the concrete square Taylor-evaluation matrix in the monomial basis is nonsingular. Its rows are encoded by an equivalence `(Sigma i, Fin(r i)) ≃ Fin N`.

### How to apply this to the manuscript

At a repeated left-endpoint block alpha_u=...=alpha_v=alpha, let r=v-u+1. The local regularized denominator has the form

    1/Q(-alpha+w) = w^(-(v+1))*B_alpha(w),  B_alpha(0) != 0.

After reversing the block order, its leading-column functionals on a polynomial p are

    coeff_j(B_alpha(w)*p(-alpha+w)),  j=0,...,r-1.

Call `eq_zero_of_unit_weighted_jets` at the distinct nodes `-alpha`, with these multiplicities and local unit series. This discharges the root-multiplicity and unit-factor part of nondegeneracy without constructing a large confluent determinant formula.

The actual application bridge is now proved in
`Construction/ActualAuxiliary.lean`: the repeated-left-endpoint block has
exactly r columns, and the reversed local orders `mu(ell)-1-j` range over
`0,...,r-1` exactly once. The top coefficients equal the local jet
functionals with their explicit nonzero `auxiliaryScale` factors. The local
unit constant is nonzero, so `eq_zero_of_unit_weighted_jets` proves the actual
leading matrix determinant is nonzero.

The high-order vanishing at x=1 and support bounds needed for the full identity

det A(x)=c*x^a*(x-1)^N, c!=0,

are also proved. The order-N zero is transferred from the exponential-series
matrix determinant to the polynomial determinant. After factoring the
support-guaranteed power of x, the normalized determinant has degree at most
N and is divisible by `(X-1)^N`; its top coefficient is the nonzero leading
matrix determinant. Thus the full factorization has that same scalar, and
evaluation in `ℂ` proves the actual matrix `A(i)` is nonsingular. A global
all-pole partial-fraction identity is not asserted and is not needed for this
P2 proof route.

## 4. Local denominator kernel

File: `Construction/LocalDenominators.lean`.

`integerRationals` is the image subring of integers in rationals. The predicate

    DenominatorCleared d b f

means every coefficient satisfies

    d^(u+b)*coeff_u(f) is an integer.

The implementation rescales the formal variable and multiplies by d^b. This turns the convolution budget into ordinary multiplication of integral-coefficient series.

Main interfaces:

- `denominatorCleared_iff`: expose the coefficientwise mathematical meaning.
- `intervalLcm`, `boundedDistance_dvd_intervalLcm`: the actual finite lcm formula and divisibility for every nonzero signed distance with absolute value at most n; this does not import the prime number theorem.
- `DenominatorCleared.mul`, `denominatorCleared_prod`: denominator offsets add under multiplication and arbitrary finite products.
- `DenominatorCleared.add`, `denominatorCleared_sum`: equal offsets are preserved under finite sums.
- `normalizedReciprocal e`: coefficients `(-1/e)^u`; `normalizedReciprocal_identity` proves it is the inverse series of `1+w/e`.
- `regularReciprocal e`: `1/e` times the normalized series; `regularReciprocal_identity` proves it is the inverse of `e+w` when e is nonzero.
- `normalizedReciprocal_cleared`: offset zero if e is nonzero and divides d.
- `regularReciprocal_cleared`: offset one under the same conditions.
- `normalizedReciprocal_intervalLcm`, `regularReciprocal_intervalLcm`: the preceding two bounds directly specialized to the finite lcm and bounded integer distances.
- `poleLocalProduct_cleared`: an integer constant times any product of normalized reciprocals has offset zero.
- `regularLocalSum_cleared`: an integer-weighted partial-fraction sum of regular reciprocals has offset one, irrespective of how many summands it contains.
- `polynomialNumerator_cleared`: the local numerator `(-ell+w)^h` has offset zero.
- `DenominatorCleared.coeff_with_budget`: increase the total clearing exponent to any available budget.
- `pole_regular_order_budget`, `mixedLocalProduct_coefficient`: perform the cancellation between the extraction order and the variable number of poles.

### How to apply this to the manuscript

Use `d=lcm(1,...,n)` as an integer. Every nonzero integer distance e with |e|≤n divides d. For an interval [alpha,beta], set

    H(z)=(beta-alpha)! / product_{r=alpha..beta}(z+r).

If ell lies in the interval, the local unit is

    w*H(-ell+w)
      = (-1)^(ell-alpha)*choose(beta-alpha,ell-alpha)
        * product_{r!=ell}(1+w/(r-ell))^(-1).

Apply `poleLocalProduct_cleared`, giving offset zero.

If ell lies outside, use the integer-weighted partial fractions

    H(z)=sum_r (-1)^(r-alpha)*choose(beta-alpha,r-alpha)/(z+r).

Apply `regularLocalSum_cleared`, giving offset one. Using the product of all raw reciprocals instead would lose one denominator per interval point and destroy the intended estimate.

For M factors and multiplicity mu at ell, the requested coefficient requires local order at most `mu-1-j`; there are `M-mu` regular factors. The proved convolution budget yields clearing exponent at most `M-1-j=m-j`. Multiply by the remaining integer powers of d and m!/j! to recover the normalized A coefficients.

Implemented in `Construction/ActualAuxiliary.lean`: actual nested intervals,
the signed binomial weights, the product-of-distances factorial identity,
the cleared finite partial-fraction numerator identity, and the pole and
regular local denominator identities. The actual coefficient family uses
`localCoefficient` and `actualAuxiliary`; its rational coefficients are
proved to lie in `integerRationals`, and `integerPolynomialLift` supplies an
explicit polynomial over `Z` whose rational map is `actualAuxiliary`. The
existing generic LocalDenominators results are applied directly for the
coefficient budget. Bounded-distance divisibility is reused unchanged.

P2 actual-construction checkpoint is complete. `actualAuxiliaryPolynomialDet_factorization`
proves the full identity with scalar `det(actualAuxiliaryLeadingMatrix P)`;
`actualAuxiliaryPolynomialMatrixAtI_det_ne_zero` proves nondegeneracy at i
for the mapped complex matrix. The leading determinant proof calls
`eq_zero_of_unit_weighted_jets` after establishing the block-order bijection.
The global all-pole partial-fraction decomposition described in the older
draft of this handoff remains unproved, but is not an obligation of this P2
route. P3–P7 were not run.

## 5. Horizontal tail algebra

File: `Analysis/HorizontalPair.lean`.

`horizontal_pair_tail` proves, for every real t, Y>1/2 and |u|≤1/2, the scalar inequality

    (1+t^2/B)^2
      <= 1+(2*(Y^2-u^2)*t^2+t^4)/(Y^2+u^2)^2,
    B=(Y^2+1/4)^2/(Y^2-1/4).

This is a whole-line inequality, not a local saddle expansion. Its more general coefficient-comparison lemmas are also available.

`normSq_horizontal_factor` and `paired_normSq_ratio` supply the exact identification of this scalar expression with the complex squared-modulus ratio. Remaining analysis bridge: account for an unpaired central offset, multiply over actual repeated intervals, pass from squares to positive norms and real exponents, and prove integrability/uniform domination. The rectangle contour identity, vertical-edge limits and central Stirling/Riemann-sum rate are still open. Do not advertise the pair theorem as a proof of the full contour estimate.

## 6. Recommended next tasks, in order

1. Rebuild the project and run the current axiom audit before editing. Read the verified handoff status and avoid re-proving P1.
2. P2 actual construction is accepted for this checkpoint. Its result is in `Construction/ActualAuxiliary.lean`; see section 10 and `docs/STATUS.md`.
3. Treat the P3–P7 items below as a separate explicitly started goal. Do not chain-run them as part of the P2 checkpoint.
4. Establish the signed-floor valuation estimate. Explicitly split zero coefficients or use divisibility. Never silently assume a zero convention for `padicValRat`.
5. Implement a small exact rational cell checker and prove order stability and endpoint coverage. Midpoint experiments alone do not establish a continuous-cell theorem.
6. Isolate the required prime-number theorem, build it and inspect its actual transitive axioms. The source audit in `LIBRARY_AUDIT.md` has not accepted the candidate as a dependency. Repository-wide sorries do not automatically invalidate an unrelated declaration, but text search does not establish cleanliness either.
7. Connect coefficient bounds and the full contour estimate to `AuxiliaryFamily`. Prove thresholds uniform in rows and the entire disk, with n=L*r and fixed parameters.
8. Implement rational certificates at a fixed rational height. Recover the cubic target before generalizing the numerical table.
9. Scale the fixed twelve-layer weights and prove the explicit all-odd-k recipe. Reuse the shape certificate; do not generate million-dimensional matrices.

The global contour estimates, PNT interface and exact construction remain mathematically demanding. They are not all routine leftovers. If one of them blocks progress, record the smallest precise obligation and complete independent tasks first.

## 7. Numerical and effectivity cautions

- The desired cubic target is strict `<1203.973`, represented by the exact rational `1203973/1000`.
- The root-free lower estimate at k=3,s=11 is weaker (approximately 1203.98515 in the earlier audit); it cannot by itself recover that target. Use a sufficiently close fixed rational contour height and independently verified bounds.
- Arb values in the manuscript JSON are candidate data, not Lean axioms or proof certificates.
- One-sided divisor rates suffice. You may avoid a digamma theory by using positive rational-difference series and proved tails.
- No explicit numerical q0(epsilon) is required for the irrationality-exponent theorem.

## 8. Build discipline and audit

Use selective imports; do not add `import Mathlib.Tactic` to a small module. It can trigger a large dependency rebuild. The local machine has limited free RAM; a wide cold rebuild produced misleading file-read errors and allocation failures.

If new Mathlib dependencies are uncached, fetch only their transitive cache with the existing cache executable, for example:

    lake env .lake/packages/mathlib/.lake/build/bin/cache.exe get Mathlib.Algebra.Polynomial.OfFn Mathlib.RingTheory.PowerSeries.Inverse

Use a small worker setting when needed:

    $env:LEAN_NUM_THREADS='2'
    lake build
    lake env lean AxiomAudit.lean

Do not clean `.lake` or repeat the original toolchain installation without evidence. Keep logs concise: inspect relevant error contexts rather than repeatedly dumping full LEAN_PATH traces.

The trust criterion is the final theorem's transitive axiom set, not the presence of `#print axioms` in an unexecuted file or a repository-wide text scan.

## 9. Final verification record

Accepted on 27 October 2026:

- Complete library build: exit 0; `logs/hard-core-final-build.log`, 3079 build jobs including cached dependencies. The three new modules and the library root were rebuilt successfully; the final build contains no warnings.
- `lake env lean AxiomAudit.lean`: exit 0; `logs/hard-core-final-axioms.log`, 85 checked declarations. The union of reported axioms is exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or native-evaluation axiom was reported.
- Source scan of the 25 project modules: no `sorry`, `admit` or `axiom` declarations. The project has about 1915 source lines; the three new kernel modules have 41 theorem declarations across 518 lines. These counts are not a percentage of the full research goal.
- The original P1 build failure is fixed, and the abstract theorem's public input has not been weakened to assume its conclusion.

The narrowed difficult-kernel checkpoint is complete. The original full numerical/formalization goal is not. Use this distinction when reporting progress or creating the next goal.

The provided `../START_LUNA_MAX.txt` was the bounded prompt for the P2
checkpoint, now completed in section 10. Do not replay it; any P3–P7 work
requires a separately started goal.

## 10. P2 actual-construction checkpoint, 27 October 2026

P2 actual auxiliary construction is complete. `Construction/ActualAuxiliary.lean`
is imported by the library root. It proves the interval/local-expansion and
partial-fraction coefficient identities, applies the existing
`LocalDenominators` kernel to establish integrality of A, proves support and
degree bounds, and identifies the leading columns with the local jets.
Repeated left endpoints are shown to index the jet orders exactly, and
`eq_zero_of_unit_weighted_jets` proves the leading determinant nonzero. The
order-N zero at 1, full factorization

    det A(X) = det(leading matrix) * X^(sum left endpoints)
                 * (X - 1)^(sum interval lengths),

and nonsingularity of the actual complex matrix A(i) are proved. The
all-pole partial-fraction identity from the older draft is not claimed and
is not required for this proof route. P3–P7 were not run.

The complete build passed with 3109 jobs; see
`logs/p2-actual-final-build.log`. `lake env lean AxiomAudit.lean` passed with
125 output lines covering 109 `#print axioms` checks, including all new P2
results; the union of reported axioms is exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or `native_decide`.
The Lean source scan found no `sorry`, `admit`, or `axiom` declarations.
The project remains on Lean/Mathlib v4.35.0 and the locked manifest revision.

## 11. Independent P2 acceptance and next goal

P2 was independently rechecked on 27 October 2026: the full build passed,
and 109 axiom checks reported only `propext`, `Classical.choice`, `Quot.sound`.
Logs are `logs/p2-review-build.log` and `logs/p2-review-axioms.log`.
There are 39 style/deprecation warnings, with no build or axiom-check errors.

See `../P2_REVIEW_2026-10-27.md` for the acceptance report. The next assigned
scope is P3-A, specified in `../P3_ARITHMETIC_GOAL.md`; a copyable launch prompt
is `../START_P3_GOAL.txt`. This replaces replaying the completed P2 launch prompt.

P3-A proves prime-power divisibility of the actual integer coefficients, a
positive finite-pole-minimum common divisor, the integer quotient family and
its nonzero determinant at i. It includes a nontrivial n=42,p=41 instance.
Continuous cell certificates, PNT/gamma, full contours and numeric bounds are
separate later goals. Stop for acceptance when P3-A is complete.

## 12. P2-scope revalidation, 27 October 2026

The P2 handoff was rechecked against the current library root. `lake build`
passed with 3109 jobs (`logs/p2-request-build.log`).
`lake env lean AxiomAudit.lean` passed; the audit contains 109 checks, including
`actualAuxiliaryPolynomialDet_factorization` and
`actualAuxiliaryPolynomialMatrixAtI_det_ne_zero`, and the reported axiom union
is exactly `propext`, `Classical.choice`, and `Quot.sound`
(`logs/p2-request-axioms.log`). A Lean-source scan found no `sorry`, `admit`,
or `axiom` declarations. The toolchain and Mathlib remain pinned at v4.35.0.
The files under `OddPiPowers/Arithmetic` are outside the library root and were
not built or audited by this P2-scope check. No P3–P7 obligation was advanced.

## 13. Fresh P2 handoff verification, 27 October 2026

The current P2 checkpoint was rebuilt and audited again for this handoff.
`lake build` exited successfully after 3109 build jobs; it emitted 39 linter
warnings and no build errors (`logs/p2-current-build.log`).
`lake env lean AxiomAudit.lean` exited successfully with all 109 declared
checks (`logs/p2-current-axioms.log`). Every reported transitive axiom set is
contained in `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or
`native_decide` appears in the audit output. A scan of Lean sources found no
`sorry`, `admit`, or `axiom` declarations. The P2 root import still includes
`Construction/ActualAuxiliary.lean`; no P3–P7 modules were added to the root
or built as part of this task.

## 14. P3-A integrated acceptance and current P3-B assignment

This is the latest scope record, dated 27 October 2026. Sections 12–13 above
describe historical P2-only checks; they do not restrict the current task.
P3-A is now accepted. Continue with `../P3B_CELL_CERTIFICATE_GOAL.md` and
`../START_P3B_GOAL.txt`, not an old P2 launch prompt.

The five existing arithmetic modules were individually compiled but absent
from the library root and audit. Independent review added their root imports
and 22 audit declarations without changing mathematical proofs. The complete
build passed with 3116 jobs, exit 0 (`logs/p3-integration-review-build.log`).
The executed audit passed with 131 declarations, exit 0; axiom union exactly
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx` or
native-evaluation axiom (`logs/p3-integration-review-axioms.log`). See
`../P3A_REVIEW_2026-10-27.md` for the review.

Accepted APIs include signed carries, zero-safe local valuations, actual
coefficient prime-power divisibility, `carryWeightMinimum`, the positive
`actualAuxiliaryPrimeDivisor`, integer quotient reconstruction and its
nonsingular matrix at i, and the n=42,p=41 divisibility example.

P3-B must supply a finite rational certificate checker sound for all real z,y;
complete two-layer L=14 and twelve-layer L=69, weights (6,1,...,1), certificate
instances; weight scaling; and the connection to the actual finite-pole
minimum and coefficient divisor. Include a continuous-certificate derivation
of n=42,p=41. Midpoint samples and merged JSON intervals alone are insufficient;
handle all y endpoints, cyclic wraparound, coincident branches and zero values
at fine z-cell boundaries. External data are candidate certificates only.

Stop after P3-B root integration, complete build, transitive axiom audit and
handoff. PNT/gamma, contours and final numerical bounds are later goals.

## 15. P2-only handoff revalidation, 27 October 2026

The current request was scoped to P2 actual auxiliary-polynomial construction
and explicitly stopped before P3-B through P7. The P2 implementation was
already present and accepted; this run rechecked its source entry points,
rebuilt the current library root, executed the audit, and refreshed this
handoff. No P3-B cell-certificate work was started.

The pinned toolchain remains `leanprover/lean4:v4.35.0`; the existing
`lake-manifest.json` was preserved. `OddPiPowers/Construction/ActualAuxiliary.lean`
is imported by `OddPiPowers.lean`. It contains the actual interval family,
local expansions and partial-fraction coefficients, the factorial/binomial
identities, the application of `LocalDenominators` to coefficient integrality,
support and high-order vanishing, and the leading-matrix identification with
`eq_zero_of_unit_weighted_jets`. The full determinant factorization and the
nonzero determinant at `Complex.I` remain the stated P2 results.

`lake build` passed with 3116 jobs and 61 warning lines, with no errors; the
current root includes the previously accepted P1/P2 and P3-A imports and the
horizontal-pair kernel. The executed
`lake env lean AxiomAudit.lean` passed with 131 checks, including
`actualAuxiliary_integerRationalPolynomial`,
`actualAuxiliaryLeadingMatrix_det_ne_zero`,
`actualAuxiliaryPolynomialDet_factorization`, and
`actualAuxiliaryPolynomialMatrixAtI_det_ne_zero`. The union of reported
transitive axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or `native_decide`. A source scan found no `sorry`,
`admit`, or `axiom` declarations under `OddPiPowers/`.

Logs: `logs/p2-al-final-build.log` and `logs/p2-al-final-axioms.log`.
P3-B remains a separate open goal; do not continue it as part of this P2
handoff.

## 16. P3-B remains a separate open scope

At the time this section was written, the user had authorized continuing the
next step. The current request, dated 28 October 2026, is instead explicitly
scoped to P2 actual construction; preserve the partial P3-B files without
advancing them as part of this P2 handoff.

The previous run did write partial P3-B source before returning to P2 review:
`Arithmetic/ContinuousCarry.lean` contains periodicity, boundary indicators,
weight scaling and the complete positive two-layer interval bound;
`Arithmetic/CertifiedPrimeDivisor.lean` contains grouped actual-interval and
divisor bridges and the continuous 41-divisibility example. These modules are
not imported by the root and their final declarations are not covered by the
131-entry root audit. They are not yet an accepted P3-B checkpoint.

These modules remain unaccepted P3-B work. A future P3-B goal should compile
and complete them, then integrate and audit all final declarations. They are
outside the current P2-only request.

The original full goal still requires P3-B certificates, P4 divisor rates,
P5 analytic estimates and actual AuxiliaryFamily instantiation, and P6/P7
numerical and general odd-power applications. These remain separate goals.

## 17. P2-only revalidation, 28 October 2026

The current request was limited to closing and verifying the P2 actual
auxiliary-polynomial construction, without automatically continuing P3–P7.
The P2 implementation was already present and accepted, so this run rechecked
the source entry points, rebuilt the locked project, executed the axiom audit,
and refreshed the handoff. No P3-B certificate work was advanced.

The toolchain remains `leanprover/lean4:v4.35.0`; `lake-manifest.json` and the
locked Mathlib dependency were preserved (git revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`). The library root imports
`Construction/ActualAuxiliary.lean`. That module defines the actual finite
intervals, local expansions and partial-fraction coefficients; proves the
factorial/binomial identities; applies `LocalDenominators` for coefficient
integrality; proves support and high-order vanishing; and connects the leading
matrix to `eq_zero_of_unit_weighted_jets`. The complete determinant
factorization and nonzero determinant at `Complex.I` are included in the
audited root.

`lake build` passed with 3116 jobs. `lake env lean AxiomAudit.lean` passed with
131 checks, including `actualAuxiliary_integerRationalPolynomial`,
`actualAuxiliaryLeadingMatrix_det_ne_zero`,
`actualAuxiliaryPolynomialDet_factorization`, and
`actualAuxiliaryPolynomialMatrixAtI_det_ne_zero`. The transitive axiom union
is exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`,
`native_decide`, or other unproven project axiom appeared. The focused source
scan of the P2 construction and its two supporting kernels found no `sorry`,
`admit`, or `axiom` declarations.

Logs: `logs/p2-al-current-build-2026-10-28.log` and
`logs/p2-al-final-2026-10-28-audit.log`. P3-B remains open and separate; its
partial sources were not modified in this task.

## 18. P3-B pause diagnosis, 28 October 2026 — historical restart notes

The P3-B scope remains incomplete. This section preserves its prior restart
diagnosis; the current checkpoint is limited to P2 and does not resume P3-B.
For a later P3-B run, check the goal lifecycle and consult
`../P3B_PAUSE_DIAGNOSIS_2026-10-28.md`.

Actual P3-B work includes the 1180-cell table data and certificate module.
Preserve the generated table. `TwelveLayerCost.lean` now compiles as a targeted
module, repairing the earlier rewrite errors recorded in
`logs/p3b-pause-diagnosis-cost-2026-10-28.log`. However,
`TwelveLayerCells.lean` still contains 30 `native_decide` chunk proofs, and a
recent adjacent-order proof refactor is incomplete and fails to build. This
is the next P3-B blocker: replace those evaluations with kernel-checkable
proofs before integration or acceptance. The current 131-entry root audit
does not cover these draft modules. Check the goal lifecycle and user scope
before resuming that separate goal.

## 19. Confirmed memory exhaustion and restart — latest checkpoint

Windows event 2004 at 28 October 01:12:27 (UTC+8) confirms virtual-memory
exhaustion: system commit 43.605/43.711 GiB (99.76%). Two concurrent Lean
processes committed 6.81 and 2.99 GiB; a Python process committed 1.90 GiB.
The OS booted at 01:15:45 with non-clean restart events. This confirms memory
exhaustion and is consistent with the reported hang; it does not establish
the exclusive cause of the restart.

After reboot the original task's latest turn failed with `workspace routing
discovery failed`, and its persisted goal is blocked. No Lean/Lake process
was running during this inspection; the directory, source and manifest are
readable. No new compilation was started by this diagnosis.

Preserve the current adjacent-order/per-row certificate refactor. Only the
data/chunk twelve-layer modules have current compiled artifacts at inspection;
the certificate/cost chain is unaccepted. Historical statements about 30
native proofs and the earlier rewrite errors are not the current source
state. Read `../RECOVERY_AFTER_MEMORY_EXHAUSTION_2026-10-28.md` before restarting.
Restore routing, then test one small proof block with one process and an
explicit memory limit. Do not overlap compiler probes or perform a full build
as the first recovery check. Keep the toolchain, manifest and existing cache.

## 20. D-drive migration and current-chat resubmission

The user authorized resubmitting P3-B with memory control and moving project
data off C:. Migration is complete: actual storage is
`D:\codex\pi-irrationality`; the six old C: content directories are verified
compatibility junctions. All 59,067 original files passed path/size/SHA-256
verification before switching. Originals are preserved in a separate D:
rollback archive. C has about 11.5 GiB free. See
`../D_DRIVE_MIGRATION_2026-10-28.md` for paths and paging observations.

The old task stays blocked with a workspace-routing error. The continuation
has been established and read back as active in the current chat; do not revive the old task in
parallel or repeat its historical P2-only scope. Read
`../P3B_MEMORY_BOUNDED_GOAL.md` and the root `AGENTS.md` after compaction.

Use `scripts/bounded_lean.py` for proof checks: one source file, one worker,
2048 MiB Lean-internal memory cap, 6144 MiB total child-job cap, timeout,
named mutex and system headroom gates. `--emit` writes a single compiled
artifact inside the existing .lake tree. No raw unguarded build/probe.
The final cap was chosen during deployment after measuring module-import
overhead; do not raise it during proof work. Pure Lean and minimal Mathlib
checks on D passed; the latter used about 3127 MiB peak job commit. The
48 MiB hard-cap self-test also passed. No mathematical P3-B acceptance is
claimed by these environment checks.

Resume the unfinished per-row/adjacent-order certificate work. Refactor
heavy imports and proof representation when a bounded trial fails. Preserve
the exact data and existing lemmas; finish the continuous lower function,
actual divisor bridge, root integration and actual final axiom audit before
marking P3-B complete. P4/P5 and numerical bounds remain later work.

## 21. Historical pre-build checkpoint — superseded by section 22

Read `../P3B_CURRENT_CHECKPOINT.md` first. All required P3-B mathematical
modules now compile and the updated root compiles. The executed expanded
audit covers 172 distinct declarations and reports only propext,
Classical.choice and Quot.sound, with no sorryAx or native-evaluation axiom.
All 1180 twelve-layer rows are individually proved through ordinary kernel
computation in 30 modules. The full all-real bound, ordered cells, boundary
zeros, scaling, actual divisor and coefficient bridges, and continuous
n=42,p=41 instance are now included. Historical draft/native-proof blockers
in sections 17–20 are superseded by these actual compiled declarations.

Final acceptance still awaits the ongoing strict serial Lake validation of
the 72-module root dependency closure. Its exec session is **26703**; poll
that handle and verify actual liveness rather than starting another build.
The state/log manifest is `logs/p3b-guarded-library-build-state.json` for run
`20261028T023320`. The runner uses direct pinned Lake/Git, 2048 MiB Lean memory,
6144 MiB total job memory, a two-process child cap, and one target at a time.
Do not revive the old blocked task or bypass the guard. Keep this goal active
until all build and acceptance requirements are actually verified.

## 22. P3-B final acceptance, 28 October 2026

P3-B is complete and accepted. All requirements in the assigned two-layer
and twelve-layer certificate scope are covered by actual compiled Lean
declarations and the executed final axiom audit. See
`../P3B_REVIEW_2026-10-28.md` for the explicit requirement/evidence table.

The strict serial Lake validation passed every one of the 72 project targets
in the root dependency closure, including the final library root. Session
26703 exited 0; the final root log reports `Build completed successfully
(3156 jobs)`. State and per-module logs are recorded in
`logs/p3b-guarded-library-build-state.json`, run `20261028T023320`.
Every completed target's recorded source hash matches the current source,
and all guarded-job records report exit 0.

The fresh post-build `AxiomAudit.lean` run passed with exit 0 in session
73067. `logs/p3b-post-build-axioms.log` contains exactly the 172 distinct
configured declarations, without missing or duplicate entries. Its axiom
union is exactly propext, Classical.choice and Quot.sound; no sorryAx or
native-evaluation axiom is reported. A project Lean-source scan found no
sorry/admit/axiom/native_decide occurrences. The pinned v4.35.0 toolchain and
manifest remain unchanged; the manifest hash equals the original D rollback
copy. `logs/p3b-acceptance-2026-10-28.json` summarizes the verified result.

This run closed all 1180 twelve-layer rows, the whole-real certificate
soundness, boundary/gap treatment, ordered disjoint cells, periodic lower
function and boundary zeros, uniform scaling, actual divisor/coefficient
bridges and the continuous n=42,p=41 example. Source changes, build and audit
all stayed within the assigned P3-B scope. The final guarded library build
peaked at 3272.04 MiB aggregate job commit; the post-build audit at 4876.01 MiB,
below the 6144 MiB hard cap. One Lean worker was used at a time.

No P4 prime-number/gamma, P5 contour/uniform-rate, or P6/P7 final numerical
or general odd-power application is accepted here. Do not re-run P2 or
resume the obsolete blocked task. A later stage requires a new assigned
objective; retain the D-drive storage and bounded-memory workflow.


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
