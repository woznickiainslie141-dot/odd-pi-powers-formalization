# P6 general height simplification: read-only mathematical audit

The proposed direct estimate is mathematically sound for **fixed** `M` and
removes the need to prove the regular-factor product identity or the factorial
distance comparison in the earlier `P5_HEIGHT_PROOF_PLAN.md`. The earlier
claim that termwise absolute values necessarily lose an extra exponential
factor was too strong: one assigns the factor `2^(length a)` **once per
interval**, whether the interval is regular or contains the pole. The extra
`n+1` per regular interval is polynomial because `M` is fixed. This note is
an audit and implementation plan, not a Lean proof or acceptance record.

## Exact local estimates

Fix `P : OddPiPowers.ActualIntervals M`, write `n=P.n`, `m=M-1`,
`S=∑ a : Fin M, P.length a`, and consider `ell ≤ n`. In
`Construction/ActualAuxiliary.lean`,

    P.regularLocalFactor a ell =
      ∑ r ∈ P.interval a,
        C (P.binomialWeight a r) * regularReciprocal ((r:ℤ)-(ell:ℤ)).

For `ell ∉ P.interval a`, every difference is nonzero. From
`Construction/LocalDenominators.lean`, the coefficient of
`normalizedReciprocal e` at `q` is `(-1/(e:ℚ))^q`, and
`regularReciprocal e = C (1/(e:ℚ)) * normalizedReciprocal e`.
For nonzero integer `e`, both coefficient absolute values are at most 1,
including `q=0`. Then `Nat.choose_le_two_pow`, `binomialWeight`, and
`P.interval_card_eq_length_add_one` give, for **every** `q`,

    |coeff q (P.regularLocalFactor a ell)|
      ≤ (P.length a + 1) * 2^(P.length a)
      ≤ (n+1) * 2^(P.length a).

The second inequality follows from `P.length a ≤ n`. Every term in the
finite sum is bounded, so no cancellation or regular-factor denominator
identity is required. One may also prove the reciprocal bounds uniformly
for `e=0` under Lean's totalized inverse: the regular reciprocal is zero and
the normalized series has constant coefficient 1 and later coefficients 0;
the nonzero route is simpler for matching actual distance factors. In either
approach do not infer nonzero by silently excluding repeated endpoints: pole
factors explicitly erase the chosen index, while the regular branch has no
chosen index in its interval.

If `ell ∈ P.interval a`, the actual definition is

    P.poleLocalFactor a ell = C (P.binomialWeight a ell) *
      ∏ r ∈ (P.interval a).erase ell,
        normalizedReciprocal ((r:ℤ)-(ell:ℤ)).

The coefficient of `C (binomialWeight ...)` is bounded by
`2^(P.length a)` in every degree, including the zero-weight case; it is
therefore also bounded by `B_a=(n+1)*2^(P.length a)`. Give that constant
series weight `B_a`, and give each normalized reciprocal weight 1. In the
regular branch include the entire regular series as **one** factor of weight
`B_a`. This uses exactly one `2^(length a)` budget per interval in either
branch. Distinct interval occurrences and repeated distances must remain
separate list entries even when their underlying series coincide.

For the numerator `(C (-(ell:ℚ)) + X)^h`, insert `h` copies of the same
linear series, each with weight `n+1`: its constant coefficient has absolute
value `ell ≤ n`, its degree-one coefficient is 1, and all others vanish.
This covers `ell=0`, including `h=0`, with no divisions by `ell`.

## Apply the actual list majorant

The current checked source `Analysis/SeriesCoefficientMajorant.lean` exposes
`OddPiPowers.coeff_list_prod_abs_le` for a list of `(PowerSeries ℚ × ℚ)`
whose weights are nonnegative and dominate **all** coefficients:

    |coeff q (product series)| ≤ product weights * choose(T+q,q),
    T = list.length.

It also exposes `OddPiPowers.choose_coefficient_majorant_le_pow T q m hq`,
which bounds the binomial by `(T+m+1)^m` for `q≤m`. Represent the outer
family by the list of `Fin M` occurrences, and each pole's erased interval
by its own list; flatten only after forming these lists. `Finset.prod_toList`
and `Finset.length_toList` are present in Mathlib; finite-product mapping and
`List.prod_append`/`List.length_append` support the bridge. A list with
duplicate series is intentional and must never be turned into a finset of
series values.

Using the exactly one weighted head factor per interval gives

    product weights = (n+1)^(h+M) * 2^S,
    T ≤ h + M*(n+2).

The pole interval contributes one head plus at most `n+1` reciprocal factors;
the regular interval contributes one head and no reciprocal list. With
`h≤m`, `q≤m`, and `n≥0`, a safe fixed constant is
`C_M = 2*m + 1 + 2*M`, because

    T+m+1 ≤ C_M*(n+1).

Thus the proposed uniform local estimate is

    |coeff q (P.localExpansion ell h)|
      ≤ C_M^m * (n+1)^(2*m+M) * 2^S.

No denominator clearing is needed for this absolute-value estimate. The
nonzero weight and source expressions must be taken in `ℚ` with natural casts
shown explicitly; powers and sums of `length` must be converted with finite
product lemmas rather than relying on an unproved asymptotic statement.

For `h,j : Fin M` and `M>0`, the private source lemma
`ActualIntervals.multiplicity_le_M` can be reproduced from filtered-card ≤
univ-card. In the nonzero branch of `localCoefficient`,
`q=multiplicity ell-1-j≤m`; in its other branch the coefficient is 0. This
supports all repeated endpoints, multiplicity zero, `M=1`, and length zero.

## From local estimates to rates

`auxiliaryScale M n j = m! * (intervalLcm n)^m / j!`; since `j!≥1`, its
absolute value is at most `m! * d^m`, with `d=intervalLcm n`. Expanding
`actualAuxiliary` using `Polynomial.finsetSum_coeff` and
`Polynomial.coeff_C_mul_X_pow`, a coarse triangle inequality over at most
`n+1` pole indices yields

    |coeff_k (actualAuxiliary P h j)| ≤
      m! * C_M^m * d^m * (n+1)^(2*m+M+1) * 2^S.

Use `map_actualAuxiliaryInt` and `Polynomial.coeff_map` to transfer this
bound to the actual integer coefficients. For `n≥1`, replace `n+1` by
`2n` to obtain the requested `K_M*d^m*n^B*2^S` with
`B=2*m+M+1` and `K_M=m!*C_M^m*2^B`. If one proves uniqueness of
`ell ↦ n-ell` on `ell≤n`, the extra `n+1` can be removed, but it is not
needed. The rate of `2^S` remains `sum(length/n)*log 2`; the fixed-degree
polynomial and constants contribute zero after division by `n`. This is the
same exponential height rate `G0` once the independently proved `log d / n`
rate and the concrete interval-length proportions are included.

For the *Gaussian row* and transfer disk bound, `eval at i` of each integer
auxiliary polynomial adds at most `n+1` using its degree bound; summing `M`
row coefficients on `‖z‖≤2` costs at most a fixed function of `M` such as
`M*2^m`. A divided-difference bound also needs its own explicit proof (or
the existing transfer interface) and cannot be inferred solely from a single
pointwise remainder estimate. Reduction by a positive integer divisor can
only improve coefficient magnitude but is a separate optional bridge.

## Minimal proof obligations and cautions

1. Coefficients of normalized/regular reciprocals, casts of absolute values,
   and `Nat.choose_le_two_pow`; `PowerSeries.coeff_C_mul` and
   `PowerSeries.coeff_mk` are existing APIs.
2. Uniform bound on the full regular sum using `Finset.abs_sum_le_sum_abs`,
   interval membership, `P.interval_card_eq_length_add_one`, and
   `P.length_eq`/`P.left_bound`. Do not claim the pole branch is a single
   weighted series: flatten its reciprocal factors individually.
3. Exact product/length/weight identities for the occurrence list, with
   `Finset.prod_toList`, `Finset.length_toList`, `List` append/map/product,
   and `Finset.prod_pow` / finite sums of exponents as needed. Names besides
   the two `toList` lemmas need compiler/API verification.
4. `coeff_list_prod_abs_le`, `choose_coefficient_majorant_le_pow`, fixed-M
   arithmetic and local-coefficient order; verify the majorant is in the
   compiled dependency closure before importing it in a new module.
5. Actual polynomial coefficient bound, integer embedding, Gaussian row
   evaluation, and quantitative/asymptotic transfer with uniform quantifiers
   over `h,j` and all sufficiently large scales.

The constants depend strongly on `M`: this is valid for each fixed family,
including `M=187` or `M=512`, but does **not** prove a polynomial bound with
constants uniform over families where `M` itself grows with `n`. The proof
does not supply sharp divisor gamma, explicit family/grouping, transcendental
numeric certificates, an `AuxiliaryFamily`, or a final irrationality bound.
No Lean compiler or generator was run in this audit, and no proof or root
source was modified.
