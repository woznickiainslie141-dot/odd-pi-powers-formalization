# P6 prefix list-to-finset sum: helper handoff

`OddPiPowers/Arithmetic/PeriodPrefixSum.lean` is an **uncompiled proof
draft**. The helper ran no Lean, Lake, bounded runner, build, generator or
axiom audit. Main owns compilation, repair, integration and acceptance. The
helper edited no existing source, root, scripts, manifest, toolchain or cache.

The draft uses the current main sources `PeriodFloorBlock` and
`CellWindowAggregate`; confirm their current signatures and bounded-compile
status before compiling this dependent module. It proposes:

* `periodPrefixLabels_append` and the corresponding actual-sum append identity;
* an identity valid for any cell list, including duplicates, equating the
  flattened label sum with a list sum of finite period sums;
* `periodPrefixLabels_actual_sum_finset` for `cs.Nodup`, matching the required
  `(1/69)*∑ r<T ∑ c∈cs.toFinset value*periodGap` with finite sum interchange;
* `selectedCellSet_sum_val`, a bijection proof between the selected subtype
  finset `selectedCells.attach.toFinset` and the raw `selectedCells.toFinset`;
* `selected_periodPrefixLabels_actual_sum`, which specializes the previous
  identity using the candidate `selectedCells_nodup` and unfolds
  `selectedUnshrunkRate`.

The `Nodup` assumption matters only for converting a list to a finset: without
it, list occurrences contribute multiplicity. `periodPrefixLabels_append`
does not require disjointness or Nodup, and permits blockwise sums without
changing the order of cell/period labels.

Source-inspected APIs include `List.sum_toFinset f hnodup`,
`List.toFinset_range`, `Finset.sum_comm`, and `Finset.sum_bij`. Expected
compiler repair: the implicit list argument to `List.sum_toFinset`,
normalization of `flatMap`, `List.map_map` and `← h` in the induction;
`Finset.sum_comm` orientation and moving `1/69` through both finite sums;
`Finset.sum_bij` elaboration, `List.mem_toFinset`, and proving that any
subtype value belongs to `selectedCells.attach.toFinset`; and simplification
of proof-irrelevant subtype membership. If the `simp` step over `attach`
fails, use `List.mem_attach` and `List.mem_toFinset` explicitly. The main
draft `CellWindowAggregate` may change during repair, so adapt the selected
definitions to its compiled interface. No large `Finset`, `K`, or cell table
should be reduced by computation in these generic proofs.

No `sorry`, `admit`, new axiom or native evaluation is introduced. The
concrete period floor blocks, their relation to the selected cells, valid
shrunken windows, tail, final rate and P6 bound still require main's proofs.
