# P6 actual weighted series factors: helper handoff

`OddPiPowers/Analysis/ActualSeriesFactors.lean` is an **uncompiled proof
draft**. The helper ran no Lean, Lake, bounded runner, build, generator, or
axiom audit. Main alone owns compilation, repair, integration and acceptance.
No existing source, root, scripts, manifest or cache was edited.

The draft imports the checked `BalancedSeriesFactors`, including its
`normalizedReciprocal_coeff_abs_le_one` and `numeratorSeries_coeff_abs_le`,
and through it `SeriesCoefficientMajorant`. For arbitrary actual intervals it
defines `actualFactorWeight P a = (P.n+1)*2^(P.length a)` in ℚ and attempts:

* binomial-weight and regular-reciprocal coefficient bounds;
* a termwise regular-factor bound for every coefficient, assuming
  `ell ∉ P.interval a`;
* `actualLocalWeightedFactors`, containing the weighted binomial constant
  followed by all erased-interval reciprocals in the pole branch, and the
  single weighted regular series in the regular branch;
* local factor-product, scalar-product, length `≤ n+2`, nonnegative weights
  and all-order coefficient bounds;
* `actualWeightedFactors`, with `h` numerator factors and the flattened list
  of all interval lists, together with candidate expansion-product, exact
  weight `(n+1)^(h+M)*2^(∑ length)`, length `≤ h+M*(n+2)`, and uniform
  coefficient-weight bounds for `ell≤n`.

The inner `toList.map` binder is explicitly `r : ℕ`, preventing the known
natural/integer coercion ambiguity. Nested lists retain duplicate distances
and repeated intervals; neither the regular factor nor the pole binomial is
counted more than once per interval. The local bound requires no `ell≤n`;
that condition is needed for the numerator factor in the full list.

Likely compiler repair points:

1. Simplifying the integer-to-rational cast and absolute value of the
   signed binomial weight; `Nat.choose_le_two_pow` supplies the actual bound.
2. Elaboration of `PowerSeries.coeff_C_mul`, `map_sum`,
   `Finset.abs_sum_le_sum_abs`, and `mul_le_mul` in the regular branch;
   scalar/series coercions and the exact orientation of `Finset.mem_erase`.
3. `PowerSeries.coeff_C` is an `if` in the weighted pole head; the last
   `split_ifs <;> simp_all` may need explicit inequalities for each case.
4. Product rewrites from finite sets to lists and flattening: `simp` needs to
   relate maps of list products to `Finset.univ` and preserve occurrence
   multiplicities. `Finset.prod_pow_eq_pow_sum` is source-verified but its
   argument order and simplifier matching are not checked. The finite-sum
   rewrite in the full length proof is particularly likely to need an
   explicit `Finset.sum_toList` bridge.
5. Full-list weight normalization combines `pow_add`, `Finset.prod_mul_distrib`
   and powers summed over `Fin M`; separate helper equalities may be cheaper
   and more robust than the current single `simp`. The univ sum in the length
   proof and natural cast in `hcard` likewise may need explicit conversion.

No final `coeff_list_prod_abs_le` application, polynomial coefficient height,
exponential rate, numeric bound or complete `AuxiliaryFamily` is claimed.
No `sorry`, `admit`, new axiom or native evaluation is introduced. Split
local and full-list lemmas into bounded modules if main's compiler finds the
single draft too costly; do not bypass the resource contract.
