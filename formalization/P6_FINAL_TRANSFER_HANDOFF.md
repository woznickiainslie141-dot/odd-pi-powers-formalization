# P6 final transfer draft handoff

`OddPiPowers/Transfer/TwelveLayerPiCube.lean` is an **uncompiled proof draft**.
The helper ran no Lean, Lake, bounded runner, build, generator or axiom audit.
Main exclusively owns all compiler access, repair, integration and acceptance.
No existing source, root, manifest, toolchain, script or cache was edited.

The draft defines `p6TwelveLayerRows` through `actualReducedRows` and the
actual `scaledTwelveLayerActualFamily 11`, so these are the actual Gaussian
integer quotient rows, not an arbitrary assumed auxiliary family. The theorem
`p6TwelveLayer_actualFamily` attempts to apply
`actual_reduced_auxiliaryFamily` at `m=186`, `L=69`, `Y=2113/20`, and
`gamma=4543599/100000`, using the existing offset bound, definitional n/left
formulas, and `PrimeRates.p6_actualDivisor_eventually_exp_lower`. It weakens
the two rates to `D=651297284/10^6`, `G=255596306/10^6` using the proposed
`p6_actualDecay_lower` and `p6_actualGrowth_upper`.

The transfer draft then proposes the unconditional theorem

    ExponentUpperBound (Real.pi ^ 3) (42170551935/35026168),

an existential bound strictly below `1203973/1000`, and exclusion of
`LiouvilleWith` at that target. The exact arithmetic identity
`186*(D+G)/(D-2*G)=42170551935/35026168` and strict target comparison were
checked independently with Python `Fraction` for planning only; the source
attempts ordinary Lean `norm_num` for both, which is the required proof if it
compiles. This is not a claim that the theorem or numerical result is proved.

All newer imports—including `P6NumericalRates`, `P6SharpDivisorRate`, their
candidate floor blocks, and any unaccepted family construction—must be guarded
compiled and audited by main. Risks: definitional equality between
`Fin (17*11)` and `Fin (186+1)`; `hA` arithmetic and the exact offset lemma;
proof irrelevance for separately written `(by norm_num : 0<11)` in `hdiv`;
the `∀ ε` binder and scalar cast in `p6_actualDivisor_eventually_exp_lower`;
the exact arguments of `actual_reduced_auxiliaryFamily`, including the n/left
identities; unfolding `p6TwelveLayerRows` during `weaken_rates`; `norm_num`
recognition of the nonnegative `G`, positive gap and final ratio; and
visibility of `not_liouvilleWith_of_exponentUpperBound`. Keep `Fin 187`
opaque and split the final theorem from dependency checks if required.

There are no explicit analytic or rate assumptions in the proposed final
signatures, but that has meaning only once every imported theorem is actually
proved and its transitive axioms audited. The draft introduces no `sorry`,
`admit`, new mathematical axiom, or native evaluation. No final P6 acceptance
is claimed here.
