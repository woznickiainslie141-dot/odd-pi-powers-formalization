# P5-B helper draft handoff

These two new modules are **uncompiled proof drafts**. No Lean, Lake, bounded
runner, build, generator, or axiom audit was run by the helper. They are not
accepted results or evidence of kernel verification. The main chat owns the
single compiler process and should inspect and check them with the prescribed
bounded runner. No existing source, project root, manifest, toolchain or cache
was changed for this handoff.

## `Analysis/ContourExponential.lean`

Defines `contourExponential lambda n z = exp (lambda * (z + n))` and drafts:

* `contourExponential_norm_imaginary`, the exact norm `exp (-theta * z.im)`;
* `contourExponential_norm_le_strip`, bounded by `exp (|theta| * H)` for
  `|z.im| ≤ H` and `0 ≤ H`;
* `horizontalPoint_im`, exact positive/negative horizontal-line norms and
  bounds uniform in `t` (the bound uses `n * |Y|`);
* the factorization, differentiability, continuity, and iterated derivative
  identity for a general complex `lambda`.

The height nonnegativity argument is included in the strip statement, though
the proof only needs the supplied absolute-value bound. Potential proof/API
issues for the bounded check: simplification of complex real and imaginary
parts, `differentiable_id.add_const` and `.cexp`, rewriting the function and
the right-hand side in `iteratedDeriv_contourExponential`, and the precise
rewrite form of `iteratedDeriv_const_mul_field`. The available source states
`iteratedDeriv_cexp_const_mul` at the root namespace in
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`.

## `Analysis/ActualRemainderAlgebra.lean`

Defines `actualExponentialRemainder` as the finite sum of the actual auxiliary
polynomial evaluations times powers of `lambda`. The drafted theorem
`actualAuxiliary_eval_exp` converts each evaluation into a sum over
`ell < P.n + 1` with exponential `exp (lambda * (P.n - ell))` using the
natural-subtraction cast only after proving `ell ≤ P.n`. The theorem
`actualExponentialRemainder_eq_sum` interchanges that sum with the `Fin M`
sum, retaining the scale and local coefficient as one rational coefficient.

`localCoefficient_reflection` handles arbitrary complex weights, assumes only
`P.multiplicity ell ≤ M`, and reindexes over the local multiplicity before
extending by zeros to `Fin M`. Its argument also covers multiplicity zero and
repeated endpoints. The multiplicity bound is explicit because the related
existing source lemma is private; downstream may derive it from the cardinality
of a filtered `Fin M` if desired.

Potential proof/API issues for the bounded check: `Polynomial.eval₂_finsetSum`
and the simplifier's coercion from `Rat.castHom`; orientation and implicit
arguments of `Complex.exp_nat_mul`; cast simplification for `Nat.sub`; sum
commutation; definitional unfolding of the local `μ` in `hμM` and `hjlt`; and
the exact rewriting of `Fin.sum_univ_eq_sum_range`. The reflection proof follows
the existing use of `Finset.sum_range_reflect` and `Finset.sum_subset` in
`Construction/ActualAuxiliary.lean`. `Mathlib.Tactic` is intentionally broad in
this first draft; narrow it if the bounded check shows import cost is too high.

## Normalization and remaining work

`ActualIntervals.localExpansion` already contains the product of the interval
length factorials through its local factors. `auxiliaryScale` contains the
common scale and the `j!` denominator. The draft introduces no additional
factorial. The existing `partialFractionNumerator_eq` identifies the
corresponding numerator as the product of length factorials times `X ^ h`.

These algebraic drafts supply neither contour integration nor uniform
analytic estimates, numerical certificates, final irrationality-measure
bounds, or a root integration/axiom audit. All those obligations and any
compiler repairs remain for the main work. No new axiom, `sorry`, `admit`, or
native evaluation has been introduced in the draft source.


## Main integration and acceptance

The original draft status above is historical. Main narrowed the broad tactic
import, checked/repaired both files, and accepted their final source in the
complete P5-B build and fresh transitive axiom audits. See
P5B_REVIEW_2026-10-29.md. The helper did not run any compiler or generator.
