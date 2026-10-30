# P6 period-floor certificate draft handoff

`OddPiPowers/Arithmetic/PeriodFloorCertificate.lean` is an **uncompiled proof
draft**. The helper ran no Lean, Lake, bounded runner, build, generator or
axiom audit. Main exclusively owns compiler access, repair, integration and
acceptance. No existing source, root, scripts, manifest, toolchain or cache
was edited.

For `PeriodFloorRow` containing one `TwelveCellCertificate`, a natural period
and proposed natural floor, the draft defines a natural numerator

    value * (rightNumerator*leftDenominator
             - leftNumerator*rightDenominator)

and denominator

    69*(period*leftDenominator+leftNumerator)
      *(period*rightDenominator+rightNumerator).

`periodFloorActual_eq_fraction` attempts to show their quotient equals
`(value:ℝ)/69 * periodGap period (cell.left:ℝ) (cell.right:ℝ)` whenever
the left numerator and both denominators are positive and the endpoints are
strictly ordered by cross multiplication. The right numerator's positivity
is derived from these conditions, not assumed independently. The subtraction
in the natural numerator is cast only after deriving the corresponding ≤.

`periodFloorCheck scale row` is a Boolean `decide` on natural-number
positivity, endpoint ordering, and `row.floor*denominator ≤ scale*numerator`.
The draft proves both directions of the cross-product equivalence for positive
scale and denominator, then a one-direction Boolean soundness theorem. A list
checker uses `List.all` and a list sum of floor numerators, with an inductive
real-sum lower bound and append support for chunked certification. `scale` is
generic; choose `10^14` downstream. It never creates a giant rational common
denominator from the individual gap terms.

Likely bounded compilation repair points:

* `TwelveCellCertificate.left/right` are ℚ values; simplify their casts into
  ℝ using the exact available `Rat.cast_div` / natural cast lemmas. Applying
  `periodGap_eq_fraction` requires proving positivity of the left endpoint
  and real endpoint order from the natural cross inequality.
* The `Nat.cast_sub` rewrite and `field_simp` after clearing the four positive
  factors may require intermediate names and normalizing casts before `ring`.
* `div_le_div_iff₀` has to compare `floor/scale` with `numerator/denominator`;
  exact casting of the cross inequality and multiplication-order rewrites may
  need an explicitly typed `ℝ` intermediate.
* `of_decide_eq_true` elaboration for the nested conjunction, conjunction
  projections, and `List.all_eq_true`/`Bool.and_eq_true` simplification in
  the inductive block proof may require `change` or `simp` around definitions.
  `List.sum_cons`, casts and `add_div` may need more explicit `change` steps.
* If a single module is costly, split the fraction identity, row checker and
  block checker under main ownership; check dependencies only through the
  prescribed bounded workflow. No compile or axiom claim is made here.

These are bounds for the **unshrunk mathematical endpoints** of the listed
cells. They do not themselves establish a valid `CertifiedCellWindow`: actual
prime windows must use strict interior endpoints, and the total shrink loss
must be proved separately, including the period-zero cap and label injection.
The draft contains no concrete rows or generator output and no claim that a
cell is from the accepted table. It introduces no `sorry`, `admit`, new
mathematical axiom or native evaluation.
