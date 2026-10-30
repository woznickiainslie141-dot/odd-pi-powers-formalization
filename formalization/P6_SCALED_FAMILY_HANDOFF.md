# P6 scaled twelve-layer family handoff

`OddPiPowers/Construction/ScaledTwelveLayerFamily.lean` is an **uncompiled
draft**. The helper ran no Lean, Lake, bounded runner, build, generator or
axiom audit. Main owns every compiler operation and must repair, compile,
integrate and audit this source. No existing source, root, manifest, scripts
or cache was edited by the helper.

The draft defines offsets for `s>0`, `M=17*s`, and `N` by

    offset(a) = if a < 6*s then 0 else (a-6*s)/s + 1,
    P.n = 69*N, P.left(a) = offset(a)*N.

It attempts offset monotonicity, `offset ≤ 11`, the `ActualIntervals` left
bound, and definitional `n_eq`/`left_scaled` lemmas. Positivity `s>0` is an
explicit constructor argument. `N=0` is retained; downstream theorems can
impose the positivity they actually need.

The candidate equivalence maps the first `6*s` indices into layer zero, and
the rest into layer `1+(a-6*s)/s` with fiber index `(a-6*s)%s`. Its inverse
uses `k` for layer zero and `6*s+(j-1)*s+k` for `j>0`. It is used to draft
`ActualIntervals.ActualCarryGrouping` of this family against
`twelveLayerShape.scaleWeights s`. The scale operation uses `s * weight`,
so the first fiber has size `s*6` and the others size `s`; the equivalence
explicitly converts `s*6 = 6*s`. Repeated intervals remain separate entries.
No `Fin 187` matrix is expanded.

The main risks for bounded compilation are exact elaboration/simplification
of dependent sigma equality and `Fin.ext`; rewriting proof-dependent `if`s;
the argument and rewrite shape of `Nat.mul_add_div`, `Nat.div_add_mod`, and
`Nat.add_mod`; `simp` recognizing nonzero and positivity conditions; and
`omega` on expressions containing products of variable `s` by the variable
layer index. If the sigma right inverse does not simplify generically,
`fin_cases j` gives only 12 cases, each with a variable fiber index and the
same identities. Use `Nat.mul_le_mul_right`, `Nat.div_lt_iff_lt_mul hs`, and
the product identity explicitly rather than asking `omega` to solve general
nonlinear multiplication. `scaledTwelveLayerOffset_mono` does not require
`s>0`, but check the exact type of `Nat.div_le_div_right` in the pinned core.
`n_eq`/`left_eq` may need `simp [CarryShape.scaleWeights, twelveLayerShape]`
to unfold definitional projections. The inverse proofs are attempts, not
checked results; their present syntax and proof obligations may need splitting
into helper lemmas in this file or main-owned modules.

For `s=11`, `17*s=187` and the construction realizes the requested exact
layer multiplicities; a separate downstream specialization may use `norm_num`.
The draft does not prove a coefficient height, actual divisor rate, central
rate, transcendental numeric certificate, or the P6 target. It introduces no
`sorry`, `admit`, new mathematical axiom, or native evaluation.
