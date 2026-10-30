# P5-E helper handoff: factorial logarithmic rate

`OddPiPowers/Analysis/FactorialLogRate.lean` is an **uncompiled proof draft**.
The helper ran no Lean, Lake, bounded runner, build, generator or axiom audit.
It did not edit existing project sources, root, dependencies, scripts or caches.
Main owns compiler access, repair, integration and acceptance.

The main candidate theorem `scaled_log_factorial_rate` states exactly the
requested limit for fixed positive natural `L` and `k`, including totalized
expressions at `N=0`. Auxiliary statements give `log n / n → 0`,
`(log(n!) - n*log n)/n → -1`, and the corresponding scaled `log/n` limit.

The proof uses the source-verified Mathlib declarations
`Stirling.stirlingSeq_has_pos_limit_a`, `Stirling.log_stirlingSeq_formula`,
`Filter.Tendsto.log`, `Real.tendsto_pow_log_div_mul_add_atTop`,
`tendsto_const_div_atTop_nhds_zero_nat`, and
`Filter.Tendsto.const_mul_atTop'`. It rewrites Stirling's identity for
eventually positive `n`, derives `log(stirlingSeq n)/n → 0`, and handles the
`log(2n)/n` term using `log(2n) = log 2 + log n`. The scaling step composes
with `N ↦ k*N`, then uses the exact eventual decomposition

    (log((kN)!) - kN log(LN))/(LN)
      = (k/L) * ((log((kN)!) - kN log(kN))/(kN) + log(k/L)).

Everything is explicitly under positive `k`, `L` and eventual positive `N`;
no assertion is made that the nonzero-denominator identity holds at zero.

The following points require bounded compilation and possibly repair: precise
`Tendsto.congr'` equality orientation and simplification of limit targets;
inference of `tendsto_id.const_mul_atTop'` over naturals; elaboration of casts
of natural products and factorials; availability of tactic imports;
`log_mul` rewrite matching after `Nat.cast_mul`; and arithmetic normalization
after `field_simp`, especially the use of the Stirling logarithmic identity in
`nlinarith`. `Real.tendsto_pow_log_div_mul_add_atTop 1 0 1` is expected to
simplify to `log x / x → 0` when composed with natural casts. If arithmetic
normalization is expensive, split the pointwise algebraic identities and
their limit proofs into small separate modules under main's ownership.

The draft contains no `sorry`, `admit`, native evaluation, or new mathematical
axiom. It does not establish the Riemann sum, actual central rate, coefficient
height, final exponent, or the full formalization.

## Main acceptance

Main repaired composition and limit normalization, the logarithmic identity simplification, and the fixed-scaling proof. The missing full Stirling cache was avoided using a source-reproduced pinned positive-limit core in a project namespace. All final factorial declarations are compiled and included in the 50-entry new audit. The earlier draft caveats are historical; the height plan remains unproved.
