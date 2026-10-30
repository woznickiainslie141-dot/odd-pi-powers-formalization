# P6 fixed-height numerical rates: helper handoff

`OddPiPowers/Analysis/P6NumericalRates.lean` is an **uncompiled proof draft**.
The helper ran no Lean, Lake, bounded runner, build, generator or axiom audit.
Main exclusively owns compiler access, repair, integration and acceptance.
No existing source, root, scripts, manifest, toolchain or cache was edited.

The draft imports main's `TwelveLayerActualRates` and the twelve generated
`P6CentralCertificate00`–`11` sources, none assumed accepted merely because
they exist. It attempts:

* the summed central bound `9578159265851/10^10`, using
  `scaledTwelveLayer_central_sum` at `s=11`, `Y=2113/20`, and each theorem
  `p6CentralIntervalXX_lower`; only the eleven-layer sum is expanded;
* `actualDecay 186 69 (scaledTwelveLayerOffset 11) (2113/20) ≥
  605861294/10^6` using the source-verified Mathlib `Real.pi_lt_d20`;
* `actualGrowth 186 69 (scaledTwelveLayerOffset 11) ≤ 301032296/10^6`
  using `scaledTwelveLayer_shapeRelativeLength` and the source-verified
  Mathlib `Real.log_two_lt_d9`.

The individual lower rationals were inspected in the generated theorem
statements and `logs/p6-central-candidate.json`. The JSON is only a candidate
data record; the actual proof depends on the twelve ordinary Lean theorems,
and all twelve and their transitive dependencies still need main's guarded
compilation and axiom audit. The value `Y=2113/20` is a fixed rational, not an
assumed optimizer. The family has 187 rows; no `Fin 187` sum or matrix is
expanded, since the shape lemmas reindex by the twelve layers.

Likely bounded compilation repairs: elaboration of `scaledTwelveLayerOffset
11` as a function on `Fin (186+1)` versus `Fin (17*11)`; unfolding
`Fin.sum_univ_succ` only for `Fin 11`; `norm_num` normalizing rational values
such as `63/69=21/23`, `57/69=19/23`, and `51/69=17/23` consistently with
the certificate declarations; matching the expanded central sum for
`linarith`; and unification of `scaledTwelveLayer_shapeRelativeLength` with
the term in `actualGrowth`. The calculation's numerical slack is small, so
keep the exact fractions and check the final inequality with `norm_num` /
`linarith`, not rounded decimal evidence. If the sum proof is costly, prove
small partial-sum lemmas in separately guarded main-owned modules.

`Mathlib.Analysis.Real.Pi.Bounds` and `Mathlib.Analysis.Complex.ExponentialBounds`
exist as sources, but this helper did not check cache availability or
transitive import cost. Preserve the existing resource contract and build
dependencies only through main's bounded workflow. The draft introduces no
`sorry`, `admit`, new mathematical axiom or native evaluation. It does not
prove a divisor rate, complete `AuxiliaryFamily`, or the final P6 exponent.
