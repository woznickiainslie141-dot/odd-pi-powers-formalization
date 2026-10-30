# P5-C helper handoff: horizontal truncation

`OddPiPowers/Analysis/HorizontalLineLimits.lean` is an **uncompiled draft**.
The helper performed no Lean/Lake invocation, build, generator, audit, or
system-resource change. The draft is not a kernel-verified result; main owns
compiler access. It imports the main chat's anticipated `RectangleContour`
module, which was not yet present when this helper inspected the workspace.
Its assumed public definition and namespace must be checked against that module.

The draft contains:

* `horizontalPoint_affine` and `horizontal_affine_transfer`: use
  `t = x / n + 1/2` for positive `n`, transport integrability, and obtain
  the whole-line identity with factor `(n : ℂ)`.
* `intervalIntegral_symmetric_tendsto`: the symmetric truncation of any
  integrable complex function tends to its whole-line integral.
* Integrability of the upper and lower actual kernel with real horizontal
  coordinates, using the accepted P5-B estimates.
* A rectangle limit to the lower horizontal integral minus the upper one,
  and a second form as `n` times the corresponding normalized-integral
  difference. The two vertical sides use the P5-B limits with
  `h + 2 ≤ degree` derived from `h ≤ m` and `2*(m+2) ≤ degree`.

Source-checked Mathlib APIs include `Integrable.comp_add_right`,
`Integrable.comp_div`, `Measure.integral_comp_div`,
`integral_add_right_eq_self`, `intervalIntegral_tendsto_integral`, and
`intervalIntegral.integral_const_mul`. Their use and elaboration remain
unverified. In particular, expect bounded compiler repair around complex cast
simplification in `horizontalPoint_affine`, conversion of real scalar action
to complex multiplication, type inference for composed integrability, and
the integral rewrite under `Tendsto`. The rectangle proof must align
`(y : ℂ) * I` with `I * (y : ℂ)` and move `I` into each interval integral;
the current `simpa` is deliberately marked for checking. The `mul_neg`
rewrites and `omega` degree implication likewise need checking. Verify the
actual `rectangleIntegral` namespace, arity and imports when main creates it.

No finite rectangle/pole-circle contour equality is assumed or proved here.
That bridge and the subsequent analytic estimates and numerical bounds remain
open. This draft introduces no new axiom, `sorry`, `admit`, or native
evaluation. No existing source, root module, dependency, or acceptance record
was changed by the helper.


## Main integration and acceptance

The draft-status warnings above are historical. Main repaired the missing
Complex.ofReal_mul simplification, checked all affine and truncation proofs,
and accepted the final source in the complete P5-C build and fresh axiom
audits. The finite contour bridge was separately proved by main. See
P5C_REVIEW_2026-10-29.md; the helper ran no compiler or generator.
