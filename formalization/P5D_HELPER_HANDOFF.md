# P5-D helper handoff: central logarithmic integral

`OddPiPowers/Analysis/CentralLogIntegral.lean` is an **uncompiled draft**. The
helper did not run Lean, Lake, the bounded runner, a build, a generator, or an
axiom audit. Main exclusively owns those operations. No existing source, root,
dependency, cache, or acceptance record was changed.

The proposed antiderivative is

    A_Y(u) = (u/2) log(u²+Y²) - u + Y arctan(u/Y).

For `Y > 0`, its derivative is `log(sqrt(u²+Y²))`. The draft applies the
interval fundamental theorem on `[-c/2,c/2]` and simplifies the two endpoints
to obtain `(c/2) log(Y²+c²/4) - c + 2Y arctan(c/(2Y))` for `c ≥ 0`.
The positivity of `Y` is the only nonzero condition used; no division by `c`
is needed. `centralIntervalRate` adds `c - c*log c` to this integral; the
zero-width identity uses Lean's `Real.log 0` convention. The draft also states
the first derivative and the derivative of that derivative with respect to
height. These hold for all real `c` when `Y > 0`, hence include `c = 0`.

The file provides proof attempts rather than accepted results. Source-verified
APIs are `HasDerivAt.log`, `HasDerivAt.arctan`, `Real.log_sqrt`, and
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. Expect compiler repair in:

* elaboration and parenthesization of the composed `HasDerivAt` proofs,
  including `const_mul`, `div`, and `convert`;
* `field_simp` denominator normalization for `1+(u/Y)²` and
  `1+(c/(2*Y))²`, and the `ring` identities after cancellation;
* proving continuity of the log/sqrt composition via `fun_prop` with explicit
  positivity, and simplification of negated endpoint arctangents and log
  arguments;
* whether the imports directly expose all tactics and calculus lemmas. Add
  narrow imports if needed; avoid a broad import or a whole-library rebuild.

If resource use requires splitting, main may separate the primitive/integral
and rate-derivative proofs into separately guarded modules; this helper owns
only the named single module. The displayed derivative-of-derivative theorem
is for the explicit first-derivative function; deriving a theorem literally
about `deriv (deriv (centralIntervalRate c))` requires local equality around
positive `Y`, using the first-derivative theorem pointwise on `Ioi 0`.

The draft introduces no `sorry`, `admit`, new axiom or native evaluation.
It does not prove actual contour central majorants, uniform rates, or final
irrationality bounds. All compiler verification and integration remain open.

## Main integration acceptance

Main repaired pointwise derivative normalization and explicit log/sqrt continuity. The resulting source and full root compiled under the bounded runner. P5-D acceptance includes every declaration in this module among 42 new axiom checks, plus 429 regression checks. Only the usual three foundational axioms occur. The earlier uncompiled-draft caveats are historical; see P5D_REVIEW_2026-10-29.md.
