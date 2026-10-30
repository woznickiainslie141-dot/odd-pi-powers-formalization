# Library audit

## Current accepted P6 scope (30 October 2026)

P1 through P6 are accepted, including the actual twelve-layer construction
and the unconditional exponent 42170551935/35026168, strictly below1203.973.
The final build and exact axiom audits passed. Read
`formalization/P6_CURRENT_CHECKPOINT.md`, `formalization/P6_REVIEW_2026-10-30.md`
(workspace-relative paths) and `logs/p6-acceptance-2026-10-30.json`
(project-relative path). Earlier open-item lists below are historical;
in particular their statements that P6 is not numerically closed are obsolete.

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

## Version decision

The initial local Lean was 4.21.0. Source inspection of Mathlib tag v4.21.0
(commit `308445d7985027f538e281e18df29ca16ede2ba3`) found Gaussian integers,
minimal polynomials and Gauss's lemma, but no polynomial resultant under that
name and no prime number theorem. Its `NumberTheory/LSeries/Nonvanishing.lean`
describes the latter as a prerequisite, not a completed theorem. The first
dependency update also failed while cloning `Cli`; it did not establish a build.

The project now pins Lean and Mathlib v4.35.0 (Mathlib tag commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`). Candidate
PrimeNumberTheoremAnd commit `127b50e33f6033e2147921167a117af96d9ba4ea`
uses the same release. The full upstream package is not a dependency: its
transitive LeanCert checkout stalled during the earlier network fetch.
P4 now vendors only the required proof subset, preserving the pinned main
manifest and avoiding Architect, LeanCert and PrimeCert entirely. All 19
adapted modules compile in the current module format. The fresh executed
audit `logs/p4-P4PntAudit-20261028T120224.log` covers WeakPNT, its Iic and psi
forms, and theta asymptotics; their axiom union is exactly propext,
Classical.choice and Quot.sound. The P4 applications and complete root validation have also passed: 104
modules, 67 new checks and 172 regression checks; only the same three axioms. The adaptation, source hashes and
Apache-2.0 license are in OddPiPowers/Vendor/PNT and
../../scripts/vendor_pnt_core.py.

## Source-level inventory

| Need | Evidence | Work remaining |
|---|---|---|
| Gaussian integers | v4.21 `NumberTheory/Zsqrtd/GaussianInt.lean`: `GaussianInt.toComplex`, injectivity, integer norm and `EuclideanDomain` | Check current names; prove modulus ≥ 1 and maps to fraction field |
| Minimal polynomial | v4.21 `FieldTheory/Minpoly/{Basic,Field,MinpolyDiv}.lean` | Bridge Gaussian fraction field, complex root and primitive normalization |
| Gauss lemma | v4.21 `RingTheory/Polynomial/GaussLemma.lean`, including `IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` | Check hypotheses and use for descent |
| Resultant | v4.35 `RingTheory/Polynomial/Resultant/Basic.lean`: `resultant_map_map`, `resultant_eq_prod_eval` (for a split polynomial), `resultant_eq_zero_iff`, `resultant_ne_zero` | Header's TODO is stale: the required product formula exists. Bridge splitting over ℂ, injective coefficient maps, irreducibility and the selected root |
| Irrationality exponent | v4.21 `NumberTheory/Transcendental/Liouville/LiouvilleWith.lean` defines `LiouvilleWith`; no standard supremum definition was located | Prove the finite-approximation bridge explicitly |
| Jets | v4.21 `RingTheory/PowerSeries/{Basic,Inverse,Trunc}.lean` | Select representation and prove finite convolution denominator budget |
| Valuation | v4.35 `NumberTheory/Padics/PadicVal/{Defs,Basic}.lean`; `padicValNat.eq_zero_iff` includes `n = 0`, so its zero value is 0 | Use divisibility or explicit zero cases |
| Stirling | v4.21 `Analysis/SpecialFunctions/Stirling.lean` | Bridge fixed rational lengths and rate |
| Contours | v4.35 `Analysis/Complex/CauchyIntegral.lean` has rectangle and Cauchy derivative formulas | P5-A/P5-B close kernel bounds and finite pole circles; P5-C proves the rectangle comparison and actual infinite horizontal representation. Uniform heights and central rates remain open |
| PNT and lcm | Candidate `PrimeNumberTheoremAnd/Consequences.lean` has `chebyshev_asymptotic : θ ~[atTop] id` and `WeakPNT'' : ψ ~[atTop] id`. Mathlib `NumberTheory/Chebyshev.lean` has `psi_eq_log_lcmUpto`, `theta_le_log4_mul_x`, and `abs_psi_sub_theta_le_sqrt_mul_log` | Completed in P4: audited 19-module proof subset, theta/psi scaling, natural-index log-lcm limit and actual-divisor rates; see P4 review |

The candidate PNT repository contains unfinished declarations, including two
`sorry`s in `Wiener.lean`. Text search shows the two declarations are not
directly referenced by the displayed proof of `WeakPNT`, but this does not
establish the transitive axiom set. Only a kernel-level `#print axioms` check
can establish whether the particular theorem is usable.
An import-graph scan from `Consequences.lean` found nine project-local modules;
their non-Mathlib import roots are `Architect` and `Batteries`. The two
unfinished declarations occur in `Wiener.lean`. This scan is not an axiom
check and does not establish which declarations the desired theorem uses.

The official Lean v4.35.0 Windows archive was downloaded from the Lean GitHub
release after the standard release-host TLS connection failed. Its SHA-256
`893fde3f52b48c647e3edcf33844cbb61f8ef70fcd88e0536bfc83f29844081e`
matches the GitHub release asset digest. `lean --version` reports commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The locked Mathlib checkout and
transitive package revisions are in `lake-manifest.json`.

Use integers or rationals for signed floor expressions, natural numbers for
positive indices and factorials, and real casts for rates. Fix `k`, `m` and all
interval parameters before the limit along `n=L*r`, normalized by `n`.


## Historical P5-B contour API decision

The pinned CauchyIntegral higher-derivative formula is centered at the pole;
its TODO still requests a general interior-point version. P5-B uses radius-1/4
circles centered at each integer pole and proves the other principal parts
holomorphic on those disks. This gives actual finite contour integrals using
the existing Cauchy-Goursat and higher Cauchy formulas, with no residue theorem
assumed. ExpDeriv supplies the iterated exponential derivative. Exact norm
estimates and Bochner/interval integrability give horizontal and vertical bounds.
The finite circle/rectangle comparison is not supplied by these APIs and is
still a substantive remaining contour proof. See the P5-B mathematical notes.


## P5-C rectangular comparison

The previously missing actual contour comparison is now proved locally.
RectangleLog computes a real simple pole with logarithm primitives and exact
argument jumps. RectangleInversePowers proves the off-pole primitive for
higher inverse powers. Complex.differentiableOn_dslope, from the pinned
RemovableSingularity module, makes the entire divided difference entire;
induction gives rectangle/circle comparison for arbitrary pole order and an
entire numerator. Actual principal sums then give the full finite comparison.
Haar affine change of variables and IntegralEqImproper truncation limits,
with the accepted P5-B vertical estimates, close the full horizontal formula.
No library patch or assumed residue theorem is introduced. All new and
regression axiom closures passed; see the P5-C review and mathematical notes.
