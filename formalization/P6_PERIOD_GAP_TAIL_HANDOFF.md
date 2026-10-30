# P6 finite period-gap tail: helper handoff

`OddPiPowers/Analysis/PeriodGapTail.lean` is an **uncompiled proof draft**.
The helper ran no Lean, Lake, bounded runner, build, generator or axiom audit;
main owns all compiler operations, repair, integration and acceptance. No
existing source, root, manifest, scripts or cache was edited.

The intended final statement `periodGap_finite_rational_lower` says, for
`0<a<b<1` and `1≤T≤K`,

    x - x²/2 - y + (periodGap T a b - periodGap K a b)/2
      ≤ ∑ r ∈ Finset.Ico T K, periodGap r a b,
    x=(b-a)/(T+a), y=(b-a)/(K+a).

The actual mathematical proof works under the weaker `0<a<b` and `T≤K`;
the draft retains the requested stronger assumptions for the intended window
application. The formula is valid at `T=K`: the sum is zero and the proposed
lower bound is `-x²/2`.
The sum is finite and `K` is symbolic. No numerical cells or gamma bound are
introduced.

The draft proposes: derivatives and convexity of `realPeriodGap`, integration
of the chord on a unit interval, a finite induction over `Ico T K`, an exact
logarithmic integral, and the inequalities `x-x²/2≤log(1+x)` and
`log(1+x)≤x`. The lower log inequality uses the accepted Mathlib lemma
`Real.le_log_one_add_of_nonneg` and the elementary nonnegative `x³` remainder;
the upper uses `Real.log_le_sub_one_of_pos`. The finite trapezoid sign is
`integral + (f(T)-f(K))/2 ≤ sum`, since a convex graph is below each chord.

These are **proof attempts**, not checked theorems. Anticipate substantial
bounded compiler repair, particularly:

* The exact syntactic association of inverse powers in the two derivative
  lemmas and `HasDerivAt.inv`/`.pow` simplification. Their pointwise calculus
  can be split from convexity. For the cubic monotonicity, explicitly use a
  monotone nonnegative power lemma rather than relying on `nlinarith` if it
  cannot prove `(t+a)^3 ≤ (t+b)^3`.
* `convexOn_of_hasDerivWithinAt2_nonneg` has the inspected source signature;
  check interior membership and local differentiability hypotheses.
* In `convex_unit_integral_le`, the restriction from `uIcc` to `Ici 0` may
  require `uIcc_of_le` and an explicit cast inequality before extracting
  `ht.1`. Check the `ConvexOn.2` argument order, scalar simplification,
  interval-integral monotonicity and the affine chord integral identity.
* The `Nat.le_induction` syntax, exact `Finset.sum_Ico_succ_top` argument,
  `IntervalIntegrable` of the adjacent pieces, and casting of `K+1` may need
  explicit intermediate equalities. Use `sum_integral_adjacent_intervals_Ico`
  plus a separate telescoping identity as an alternative.
* In `realPeriodGap_integral`, the integrability-on-`uIcc` direction,
  positivity of the shifted terms, log-division rewrites and `field_simp`
  goals may require explicit intermediate lemmas. No partial integral or
  external evaluation is assumed.
* `Mathlib.Analysis.Convex.Deriv` and `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`
  exist in source, but their cache status and import memory cost were not
  checked. Main should split into small modules rather than bypass the guard.

No `sorry`, `admit`, new axiom or native evaluation appears in the draft.
The window templates, exact finite gamma certificate, central-rate numeric
certificates and required final P6 exponent remain separate obligations.
