# P6 period-tail aggregation handoff

`OddPiPowers/Arithmetic/PeriodTailAggregate.lean` is an **uncompiled proof
draft**. The helper ran no Lean, Lake, bounded runner, build, generator, or
axiom audit; main exclusively owns compilation, repair, integration and
acceptance. No existing source, root, scripts, manifest, toolchain or cache
was edited.

For `1≤T≤K`, the draft defines the real list sum of the rational per-cell
tail estimates and attempts to prove

    selectedUnshrunkRate T + selectedTailRationalSum T K
      ≤ selectedUnshrunkRate K.

The intended proof converts `selectedCells` to its finset using
`selectedCells_nodup`, converts to the selected-cell subtype finset via
`selectedCellSet_sum_val`, applies `periodTailRational_le` to every cell,
commutes the two finite sums, and splits `range K` into `range T` and
`Ico T K`. Endpoint positivity comes from `selectedCell_left_lower`; strict
endpoint ordering comes from accepted table validity. No `right < 1` extra
hypothesis is needed for `periodTailRational_le` as currently stated.

`selectedTemplateRate_ge_prefix_add_tail` then combines independent real
lower bounds for the unshrunk prefix and the rational tail with
`selectedCellTemplate_rate_lower K`, subtracting exactly its explicit loss.
The companion theorem takes the prefix lower bound in the label-list form
used by `periodBlockCheck_sound`, relying on
`selected_periodPrefixLabels_actual_sum`. No certificate numerators, finite
table values, numerical gamma result or asymptotic assumption are introduced.
The theorem remains meaningful at `T=K`; the finite tail is empty and the
per-cell rational lower bounds may be negative.

The draft imports `PeriodTailFloor` and `PeriodPrefixSum`, both main-owned
dependencies whose source/probe status may change. Likely bounded-compiler
repairs: the direction and implicit function argument of `List.sum_toFinset`
and `selectedCellSet_sum_val`; coercion of `periodTailRational` from ℚ to ℝ;
the `Finset.mul_sum` rewrite and `Finset.sum_comm` orientation under nested
sums; normalization of `(value/69)*gap` to `(1/69)*(value*gap)`; exact
argument order of `Finset.sum_range_add_sum_Ico`; and simplification of the
`range T` label-list equality and the relative-shrink loss term. The template
and selected-cell definitions may be renamed while main repairs their source.
Split list/finset transfer, finite-range split and final comparison into small
modules if required by the memory contract.

No `sorry`, `admit`, new axiom or native evaluation is introduced. Actual
row certificates, positive gap, scaled actual-divisor application, fixed-height
numeric bounds and the final strict P6 target remain independent obligations.
