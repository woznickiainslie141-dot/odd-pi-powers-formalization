# P6 fine-cell window aggregation: helper handoff

`OddPiPowers/Arithmetic/CellWindowAggregate.lean` is an **uncompiled proof
draft**. The helper did not run Lean, Lake, bounded runner, build, generator,
or axiom audit. Main exclusively owns compilation, repair, integration and
acceptance. No existing source, root, scripts, manifest, toolchain or cache
was edited. The imported `ShrunkenCellWindows` is main's current source; its
compilation status must be confirmed by main before this module is checked.

The draft filters the accepted twelve-layer table by positive value, value
≤17, positive left numerator, and `leftDenominator ≤ 69*leftNumerator`.
It attempts to derive table `Nodup` from the accepted pairwise endpoint order
and each row's strict endpoint inequality; the selected list inherits Nodup.
It uses the selected-list membership subtype and `selectedCells.attach.toFinset`
as the finite template index set, so repeated values cannot be silently
identified. The candidate list length and finset-card bounds are ≤1180.

For every selected cell it defines a template via `shrunkenCellWindow` with
`ε=1/10^24`, proves cell-label injection and derives the base cap `69*a≥1`
from the natural cross inequality and the valid positive denominator. Important:
`shrunkenCellWindow` shrinks by `ε*(right-left)`, not by a fixed additive `ε`.
The selected predicates themselves are not asserted for every positive table
row; any concrete numerical lower bound must use exactly the selected list or
prove that omitted rows are harmless.

`selectedUnshrunkRate K` is a double sum over periods and selected subtype
cells, and the draft proposes the quantitative comparison

    selectedUnshrunkRate K -
      2*69^2*ε*K*17*1180/69
      ≤ periodWindowRate K selectedCellSet selectedCellTemplate.

It uses `periodGap_shrink_loss` per cell, value ≤17, and card ≤1180. `K` is
symbolic; no period list or certificate table is unfolded. To connect a
list-based integer-floor certificate to this finset double sum, main still
needs an explicit `attach.toFinset` list/finset sum bridge using selected
Nodup, and a proof that its certificate row order/period indexing matches the
selected list. This draft does not claim those identities are automatic.

Likely compiler repairs include: `List.mem_filter` and `of_decide_eq_true`
orientation; `List.length_filter_le` signature; generalizing `hv` and `ho`
in the ordered-list induction; `List.toFinset_card_le` implicit arguments and
length of `List.attach`; proof-irrelevant subtype equality; converting
`TwelveCellCertificate.Valid` to its first denominator field; `Rat.cast_div`
and `le_div_iff₀` in the cap proof; definitional unfolding of the template
in the shrink lemma; and simplification/normalization of finite sums and
casts in the aggregate inequality. In particular, the multiplication of the
cardinality inequality by the positive error constant may need an explicit
`mul_le_mul_of_nonneg_left` rather than relying on `nlinarith`. Split the
list/filter, templates and rate modules if the bounded compiler requires it.

The simple loss grows linearly in `K`, so the chosen ε must be kept small;
for any concrete `K`, prove the rational error budget independently. This
module adds no numeric gamma theorem, floor data, or final P6 result, and
contains no `sorry`, `admit`, new axiom or native evaluation.
