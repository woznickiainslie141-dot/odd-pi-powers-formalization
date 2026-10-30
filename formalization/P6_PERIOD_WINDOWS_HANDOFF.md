# P6 symbolic finite-period window family: helper handoff

`OddPiPowers/Arithmetic/PeriodWindowFamily.lean` is an **uncompiled draft**.
The helper ran no Lean, Lake, bounded runner, build, generator or axiom audit.
Main exclusively owns compilation, repair, integration and acceptance. No
existing source, root, scripts, manifest, toolchain or cache was edited.

The draft imports the accepted `Arithmetic.ScaledPrimeRates` and defines:

* `CertifiedCellWindow.atPeriod V r`, copying the template's existing `cell`,
  `mem_table`, `a`, `b`, `left_lt`, `a_lt_b`, `right_gt` while replacing only
  `.period` by `r`;
* `periodWindowIndices K s = (Finset.range K).product s` and the corresponding
  `periodWindowFamily`;
* a label-injectivity lemma from `Set.InjOn (fun i => (V i).cell) ↑s`;
* a cap lemma from `1 ≤ 69*(V i).a` for every template in `s`, independent of
  its original `.period`;
* `periodWindowRate`, and a candidate identity with the accepted
  `finiteWindowRate`, expressing the exact double sum of
  `cell.value * periodGap r a b / 69`;
* an eventual lower bound for the actual divisor of any family grouped by
  `twelveLayerShape.scaleWeights u`, by applying the existing
  `twelveLayer_scaled_actualDivisor_eventually_exp_lower`.

`K` stays symbolic throughout. The theorem set is finite, and no attempt is
made to enumerate a large `K`, prove a tail estimate, choose the 1180 table
templates, or assert a numerical gamma lower bound. `K=0` and an empty
template set are permitted; such a wrapper gives no positive rate by itself.
The template's original period is deliberately irrelevant to the cap and
rate after `atPeriod`; no assumption `V i.period=0` is needed.

Likely compilation repairs: elaboration of `Set.InjOn` membership after
coercion of `Finset.product`, `Finset.mem_product` and `Prod.ext`; simplification
of the record update's projections and `CertifiedCellWindow.toWindow.lower`;
`Finset.sum_product` orientation and whether it rewrites the sum underlying
`finiteWindowRate`; natural-to-real casts of cell weights and the expression
`(1/69)*sum = sum/69`; and inference of the implicit `M`, index type and
`η` in the application of `twelveLayer_scaled_actualDivisor_eventually_exp_lower`.
The rate proof currently unfolds `CertifiedCellWindow.toWindow` and `periodGap`
directly; using the accepted `CertifiedCellWindow.rate_identity` for each
product index may be more robust if elaboration fails. Check whether the
explicit `Finset.Sigma` import is already cached and needed; only the guarded
main process may resolve dependencies.

This draft has no `sorry`, `admit`, new mathematical axiom, native evaluation
or analytic assumption beyond the existing grouped-family and window-template
hypotheses. Concrete templates, strict endpoint/cap certificates, symbolic
finite tail lower bounds and the gamma and final P6 numerical theorems remain
open.
