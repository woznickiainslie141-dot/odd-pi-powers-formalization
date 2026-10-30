# Uniform coefficient height: implementation plan (read-only audit)

This is a proposed proof, not a Lean theorem or an acceptance record. No
compiler, generator, or axiom audit was run for this note. The required scope
is fixed matrix size `M > 0`, `m = M - 1`, varying actual interval data
`P : OddPiPowers.ActualIntervals M` with `n = P.n ≥ 1`, all `h,j : Fin M`,
and all polynomial coefficients. Constants and polynomial exponents may
depend on `M` but must not depend on `n`, `P`, the row, or the column.
Let `d = OddPiPowers.intervalLcm n` and `S = ∑ a : Fin M, P.length a`.
The target is a concrete bound of the form `K_M * d^m * n^B_M * 2^S`.

## Existing definitions and exact proof entry points

`OddPiPowers.Construction.ActualAuxiliary` defines in namespace
`OddPiPowers.ActualIntervals`: `length`, `interval`, `multiplicity`,
`binomialWeight`, `poleLocalFactor`, `regularLocalFactor`, `localFactor`,
`localExpansion`, `localCoefficient`; the root namespace contains
`auxiliaryScale`, `actualAuxiliary`, `actualAuxiliaryInt` and
`map_actualAuxiliaryInt`. The relevant definition is

    localExpansion ell h = (C (-(ell:ℚ)) + X)^h * ∏ a, localFactor a ell
    auxiliaryScale M n j = (m! : ℚ) * d^m / (j! : ℚ).

The order used in `localCoefficient` is `q = multiplicity ell - 1 - j`,
only if `j < multiplicity ell`, and it is zero otherwise. Since the
multiplicity counts a filtered `Fin M`, it is at most `M`; thus every used
order satisfies `q ≤ m`. This is the reason polynomial bounds in `n` suffice.
This includes repeated poles, zero multiplicity and zero-width intervals;
do not assume endpoints are distinct. Existing `multiplicity_le_M` is private,
so prove a public local lemma from `Finset.card_le_card` and `multiplicity`.

`poleLocalFactor a ell` is `C (binomialWeight a ell)` times normalized
reciprocals for `r ∈ (interval a).erase ell`. `regularLocalFactor a ell` is
currently an alternating **sum** of binomial-weighted `regularReciprocal`s;
bounding this sum term by term introduces an avoidable factor of roughly
`2^length` for every regular interval and does not establish the desired
sharp product of only the pole binomial constants. First replace the regular
factor by its exact product form below. `localFactor_mul_intervalLocalDenominator`,
`poleLocalFactor_mul_localDenominator`, and
`regularLocalFactor_mul_localDenominator` already prove the necessary
denominator identities; `clearedPartialFractionPolynomial_eq_factorial`
establishes the factorial numerator. The factorial is already included in
each `localFactor`: do not multiply it again in the bound.

`OddPiPowers.normalizedReciprocal e` in `Construction.LocalDenominators`
has coefficient `(-1/e)^q` by `PowerSeries.coeff_mk` and definition;
`normalizedReciprocal_identity` and `regularReciprocal_identity` give the
unit identities. For nonzero integer `e`, `|e| ≥ 1`, so all its normalized
reciprocal coefficients have absolute value at most 1. `PowerSeries.coeff_mul`
and `PowerSeries.coeff_prod` are available in Mathlib; the former is often
easier for induction. `Nat.choose_le_two_pow` is in
`Mathlib.Data.Nat.Choose.Bounds`.

## New lemmas in a suggested dependency order

1. **Distances and product form.** For `ell ∉ interval a`, define
   `e_r = (r:ℤ) - (ell:ℤ)` and prove all `e_r ≠ 0`. Derive

       regularLocalFactor a ell = C ( (length a)! / ∏_{r in interval a} e_r ) *
         ∏_{r in interval a} normalizedReciprocal e_r.

   Interpret casts to `ℚ` explicitly. Prove it using the existing denominator
   clearing identity and multiplication by the explicit inverse product;
   avoid adding a new axiom or defining a new supposedly equal series without
   proving equality. For `ell` outside the consecutive interval, each distance
   product has absolute value at least `(length a + 1)!`: the nearest external
   point has distances `1,...,length+1`, and any farther point increases
   each distance. Consequently the absolute value of the displayed scalar is
   at most `1/(length+1) ≤ 1`. This requires separate `ell < left a` and
   `right a < ell` cases; use `interval_mem_iff`, `length_eq`, product shifts,
   `Nat.factorial`, and monotone finite products. The `length=0` case remains
   valid. Alternatively a weaker direct comparison with `length!` is enough.

2. **Pole constant.** For every pole occurrence,
   `|binomialWeight a ell| = (Nat.choose (P.length a) (ell-P.left a) : ℚ)`
   and hence is at most `2^(P.length a)`. Use sign norm and
   `Nat.choose_le_two_pow`. In the regular case the scalar is bounded by 1,
   hence by `2^(P.length a)`. Multiplying across all `M` intervals costs
   exactly `2^S`; no second factor of that exponential size is allowed.

3. **Fixed-order reciprocal product.** For a finite set `T` of `Q` nonzero
   integer distances, let `G = ∏ e in T, normalizedReciprocal e`. Prove
   `|coeff q G| ≤ (Q+1)^q`. One elementary induction uses `coeff_mul` and
   bounds a convolution with one more reciprocal by
   `∑_{i=0}^q (Q+1)^i ≤ (Q+2)^q`; prove this inequality from the binomial
   theorem (each relevant binomial coefficient is at least one). Handle
   `q=0` and the empty product explicitly. Alternatively use `coeff_prod`
   and inject weak compositions of `q` among `Q` factors into words of length
   `q` over `Q+1` symbols. The factor count including repetitions across
   intervals is `Q ≤ ∑ a (length a + 1) ≤ M*(n+1)`. Repeated integer
   distances remain separate factors; use a disjoint index `(a,r)` or nested
   products, not a finset of distance values that silently deduplicates them.

4. **Numerator and local coefficient.** For `ell ≤ n`, `h ≤ m`, bound the
   coefficients of `(C (-ell)+X)^h` by `2^m*(n+1)^m`, e.g. via the binomial
   theorem; use `Nat.choose_le_two_pow`. Convolve with the reciprocal bound
   for `q ≤ m`, retaining at most `m+1` summands. Combining the scalar
   product and `Q+1 ≤ (M+1)*(n+1)` yields the explicit safe bound

       |localCoefficient ell h j| ≤
         (m+1)*2^m*(M+1)^m * (n+1)^(2*m) * 2^S.

   The branch `j ≥ multiplicity ell` is identically zero. The displayed
   bound deliberately avoids optimizing constants and holds uniformly in all
   rows/columns. Cast absolute values consistently to `ℝ`, or work in `ℚ`
   until the final cast; denominators and orders are algebraic facts and do
   not require analytic assumptions.

5. **Actual integer coefficients.** Expand `actualAuxiliary` using
   `Polynomial.finsetSum_coeff` and `Polynomial.coeff_C_mul_X_pow`. A coarse
   sum over `n+1` possible `ell` is sufficient; proving the sharper unique
   term via injectivity of `ell ↦ n-ell` is optional. Since `j! ≥ 1` and
   `d ≥ 1`, `|auxiliaryScale M n j| ≤ m!*d^m`. Together with `n≥1`,
   `(n+1)^(2m+1) ≤ 2^(2m+1)*n^(2m+1)` gives one concrete choice

       B = 2m+1,
       K = m! * (m+1) * 2^m * (M+1)^m * 2^(2m+1).

   This bounds every coefficient of `actualAuxiliary` in absolute value.
   Transfer to integer coefficients via `map_actualAuxiliaryInt` and
   `Polynomial.coeff_map`, preserving the norm under integer/rational casts.
   A one-term coefficient proof can drop one `n+1`, but is unnecessary.

6. **Reduced rows and transfer height.** If a bound for reduced Gaussian
   rows is required, first use `ActualIntervals.reducedAuxiliaryInt_mul`
   from `Arithmetic.ReducedAuxiliary` and
   `actualAuxiliaryPrimeDivisor_pos`: the positive integer divisor is at
   least one, so division does not enlarge integer coefficient absolute
   values. Evaluation at `i` of a polynomial of degree ≤ n costs at most
   another `n+1`; a row polynomial in `z` with `M` terms and `‖z‖ ≤ 2`
   costs at most `M*2^m`, independent of `n`. This gives a safe bound with
   exponent `B+1`, then convert to the height interface expected by
   `Transfer.OneScale`/`Transfer.Selection`. Verify the exact reduced-row
   representation and all casts before stating the final theorem: a raw
   coefficient height bound alone is not the transfer theorem's eval bound.

## Analytic alternative and tradeoff

A Cauchy coefficient bound at a *fixed* radius such as `1/2` is unsuitable:
the product of `Q = O(n)` normalized factors can add an unwanted exponential
in `n`. A shrinking radius avoids that: put `ρ = 1/(2*(Q+1))`. Each
normalized factor is bounded by `(1-ρ)^(-1)` and their product by at most 2,
using `(1-ρ)^Q ≥ 1-Qρ ≥ 1/2` (Bernoulli). The Cauchy bound is then
`2*(2*(Q+1))^q`, still polynomial for `q ≤ m`, so it preserves `2^S`.
However Lean must connect the formal rational power series to complex analytic
functions, supply nonvanishing on a circle, derive exact Taylor coefficients,
and prove the Cauchy estimate. The formal power-series convolution route
appears smaller and avoids contour machinery. A weighted finite coefficient
majorant at the same `ρ` may obtain the same bound purely algebraically.

## Main risks and acceptance boundary

The hard step is proving the regular product identity and its scalar bound
without taking absolute values before cancellation. Other risks are the
correct cardinality with duplicate distances, bridging ℚ/ℤ/ℝ absolute values,
the `M=1`, `length=0`, `ell=0,n`, and `n=1` cases, and showing every
constant is uniform in `P,h,j`. Fixed `M` is essential: if `M` varies with
`n`, the displayed `K_M` and `B_M` do not give a uniform polynomial bound.
No claims of kernel verification, numerical exponents, or completion of P6
are made here. Main should split modules and use only the required bounded
runner, then integrate the exact statement and audit its transitive axioms.
