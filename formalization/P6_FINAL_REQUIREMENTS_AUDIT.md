# P6 final requirements audit — 30 October 2026

## Executed completion addendum

The original checklist below was written before compilation and remains a
historical read-only assessment. Main has now executed its required gates:
264-module guarded validation including a fresh root (4123 dependency jobs),
424 exact new and602 exact regression axiom checks, and
`scripts/verify_p6_acceptance.py` returning `accepted`.
The four compiled final signatures are printed in
`OddPiPowers/logs/p6-post-build-axioms.log`; the fixed exponent theorem has
no mathematical hypotheses. Only propext, Classical.choice and Quot.sound
occur. All163 prior mathematical sources, pinned toolchain/manifest and
PNT/Stirling provenance passed hash checks. The full requirement-by-requirement
completion audit is in `P6_REVIEW_2026-10-30.md`; the accepted result and exact
evidence are in `OddPiPowers/logs/p6-acceptance-2026-10-30.json`.
All P6 obligations are closed. General odd-power applications remain P7.

## Historical pre-acceptance checklist

This is a **read-only audit and acceptance checklist**, not a proof or final
acceptance. No compiler, Lean, Lake, bounded runner, build, generator or axiom
audit was run for this note. The already accepted P6-B theorem yields
`ExponentUpperBound (pi^3) (14819/2)` and a strict bound below 7500; the full
P6 target `< 1203973/1000` is still open. At the main task's reported
checkpoint, all 30 prefix chunks passed their individual bounded probes and the
tail chunks were being checked serially; numerical and assembly drafts had not
yet all compiled. This is not evidence of a finished root build or audit.

## Requirement-to-source map

| Requirement | Relevant source / candidate declarations | Evidence still required |
|---|---|---|
| First unconditional instance | `Transfer/BalancedPiCube.lean`, `pi_cube_exponentUpperBound_14819_div_two`, plus `P6B_REVIEW_2026-10-29.md` | Accepted milestone; retain its source and fresh regression checks. It does not meet P6's improved target. |
| Explicit `s=11`, `M=187`, `m=186`, `L=69` actual nested family and grouping | `Construction/ScaledTwelveLayerFamily.lean`: `scaledTwelveLayerActualFamily`, `scaledTwelveLayerActualGrouping`, offset bound and n/left identities | Source probe passed per checkpoint; include exact current module in fresh dependency build and axiom audit. Do not expand `Fin 187` objects. |
| Continuous fine-cell arithmetic and endpoint correctness | Accepted `TwelveLayerCells`, `TwelveLayerCellOrder`, `TwelveLayerCertifiedBound`; `CellWindowAggregate.selectedCells` and `ShrunkenCellWindows` | Preserve the 1180 fine-cell proof, including zero-at-endpoint behavior; verify the exact selected list used by every generated chunk. Strictly interior windows and cap must be proved for each selected cell, including period 0. |
| Finite windows, PNT, actual positive common divisor | `PeriodWindowFamily`, `TwelveLayerDivisorCertificate`, accepted `ScaledPrimeRates`, `ActualPrimeDivisorRates` | Prove `(period,cell)` injection and `1≤69*lower`; use the actual `actualAuxiliaryPrimeDivisor`, and a fixed finite period set before the `N→∞` limit. No PNT or prime-rate hypothesis in the final theorem. |
| Prefix and tail numerical certificate | `PeriodFloorCertificate`, `PeriodFloorBlock`, `PeriodPrefixSum`, `P6PeriodPrefix00..29`; `Analysis/PeriodGapTail`, `PeriodTailFloor`, `PeriodTailAggregate`, `P6PeriodTail00..29`, `P6PeriodAggregate` | Complete serial bounded checks for all current chunks and all assembly modules; verify floors are paired with exactly the selected cells/periods and no truncation. The source-level rates and floor totals are not acceptance evidence until compiled and audited. |
| Divisor rate scaling | `P6SharpDivisorRate.p6_finite_window_rate_lower` and `.p6_actualDivisor_eventually_exp_lower` | Prove base `periodWindowRate ≥ 4543599/1100000`, then multiply by `s=11` to obtain `4543599/100000`; keep `η>0` and the exponent scale `69*N` in the actual eventual estimate. |
| Coefficient, disk and divided-difference height | `ActualSeriesFactors`, `ActualLocalHeight`, `ActualValueHeight`, `ActualHeightRate`, `ActualReducedDiskHeight`, `ActualReducedRates` | Source probes passed per checkpoint; root integration and transitive audits remain. Bounds must quantify uniformly over all rows and entire `‖z‖≤2` disk including the divided-difference value at its base point. |
| Actual Gaussian quotient and complete transfer family | `Construction/GaussianAuxiliaryRows`, `FiniteGaussianRows`, `ReducedGaussianRows`, `Analysis/ActualReducedFamily.actual_reduced_auxiliaryFamily`; `Transfer/TwelveLayerPiCube.p6TwelveLayerRows` | Confirm coefficients are the actual integral quotient by a positive divisor and determinant nonzero survives division; discharge `hdiv` using the actual divisor theorem, not an assumed analytic rate. |
| Central analytic rate and fixed-height numeric comparison | Accepted P5-E `ActualCentralRate`, `CentralRemainderRate`, `CentralLogIntegral`; new `TwelveLayerActualRates`, `LogRationalBounds`, `ArctanRationalBounds`, `CentralNumericBounds`, `P6CentralCertificate00..11`, `P6NumericalRates` | Guarded-compile and audit the twelve one-sided certificates and summed theorem at rational height `2113/20`. Verify reductions unfold only `Fin 11`, not `Fin 187`. Candidate JSON/Arb data cannot be proof inputs. |
| Strict transfer and final claim | `Transfer/TwelveLayerPiCube`: `p6TwelveLayer_actualFamily`, `pi_cube_exponentUpperBound_42170551935_div_35026168`, `pi_cube_exponentUpperBound_lt_1203973_div_1000`, `pi_cube_not_liouvilleWith_1203973_div_1000` | Compile with all dependencies, integrate root, execute transitive axiom audit, and check exact final signature and strict rational comparison. |

## Precise fixed-rate arithmetic to check in Lean

The intended fixed values are

    gammaLower = 4543599/100000
    D0Lower    = 605861294/1000000
    G0Upper    = 301032296/1000000
    D          = 651297284/1000000 = D0Lower + gammaLower
    G          = 255596306/1000000 = G0Upper - gammaLower.

`AuxiliaryFamily.weaken_rates` has exactly the needed directions `d≤D` and
`G≤g`; no monotonicity of an unverified quotient is assumed. Verify the final
proof actually passes its nonnegative-growth and positive-gap obligations:

    G ≥ 0,   D-2G = 140.104672 > 0,
    186*(D+G)/(D-2G) = 42170551935/35026168
      < 1203973/1000.

The margin is small. Do not use candidate decimals or introduce an unproved
equality with the full divisor's optimal rate. The proposed central-rate
lower sum is `9578159265851/10^10`; its derivation must use all 12 checked
interval inequalities with the weights `11*(6*F_1 + ∑_{j=1}^{11} F_cj)`.
The row growth uses `shapeRelativeLength=11*(347/23)` and `log 2` upper
bound. The decay term has `-(pi/2)*(2113/20)` with `pi` bounded above.
Mathlib source also contains `Real.pi_gt_d20` / `Real.pi_lt_d20` and
`Real.log_two_gt_d9` / `Real.log_two_lt_d9`; ensure any lower-bound requirement
in the final certificate is backed by an actual imported theorem, not a
printed decimal.

For the finite gamma certificate the source uses `T=32`, `K=1000000`,
`ε=10^-24` **relative to each cell width**. Prefix candidate floor is
`412848897248127/10^14`, tail candidate floor `205621482243/10^14`. The
finite shrink loss is explicitly subtracted before comparing with the base
target. The PNT theorem applies to the fixed finite range `r<K` for each
scale N, not an interchange of `K→∞` with `N→∞`. The current tail source
uses the proved-looking finite rational telescoper, rather than the superseded
helper convexity draft; only the current source and its own recorded probe
may support the result.

## Audit of assumptions and trust boundaries

* The proposed final fixed theorem signatures in `TwelveLayerPiCube.lean`
  contain no explicit mathematical hypotheses. This is only a source-level
  observation: the actual imported proof closure and final kernel constants
  have not been audited here. The generic theorem
  `actual_reduced_auxiliaryFamily` explicitly assumes the divisor rate; the
  final assembly must use the actual finite-window theorem to discharge it.
* `ExponentUpperBound` is the project's all-numerators, sufficiently-large
  positive-denominators, arbitrary-slack interface. The strict witness and
  `not_liouvilleWith` theorem make the intended interpretation concrete.
  Do not claim that the final file constructs a distinct numerical invariant
  named `μ` unless an explicit library bridge to that invariant is proved.
* Source-only word searches of the directly examined new aggregate, floor,
  tail and numeric files found no `sorry`, `admit`, `axiom`, `native_decide`
  or `unsafe` token. This is not a transitive audit: macros, imports, changed
  files and unsearched declarations can still matter. `by decide` and
  `norm_num` are ordinary proof-producing mechanisms only when the resulting
  declarations actually compile and their axioms are checked. Large generated
  candidate numerals and JSON are data, never trusted proof outputs.
* The accepted P3-B table contains 1180 fine cells, of which 1166 have
  positive values. The proof uses the filter including value and cap checks;
  a 571 merged candidate list is not a substitute without a proved sum
  identity and a separate strict-window shrink estimate. No assumption that
  all filtered rows match a candidate JSON may enter the final result.
* Rate slack, row quantifiers, endpoint membership, positivity of all
  denominators and separate integer-valued divisor handling must survive
  every rewrite. Check that `actualReducedRows` evaluates the family at
  `n/L` and is used at `n=69*N`, and that `N=0` totalized values are never
  used in an eventual-positive statement.

## Acceptance evidence still to execute

1. Finish main's serial bounded proof probes for **every current** prefix,
   tail, central and assembly source, respecting the one-process rule and
   the unchanged RAM/commit, 6144 MiB job / 2048 MiB Lean, one-worker and
   ≤300-second limits. Do not treat a previous hash or interrupted loop as
   evidence for a newly edited source.
2. Add the final transfer module to the actual root, freeze source hashes,
   and run the guarded complete dependency validation and fresh root build;
   the current root still ends at the accepted `BalancedPiCube` import.
   Reuse old records only where source identity and the documented validation
   protocol permit it; every new dependency must have its own evidence.
3. Run fresh exact-set new and regression axiom audits including the concrete
   final theorem, strict witness, family, numeric certificates, gamma and
   trust-sensitive checker declarations. Confirm the transitive axiom union
   contains only the permitted foundational axioms and no unfinished proof,
   new mathematical axiom or native-evaluation axiom.
4. Record source hashes, manifest and v4.35.0 toolchain preservation,
   generated-data provenance tied to the accepted raw cell chunks, bounded
   job exit codes and resource peaks, and final named declarations/signatures.
   Candidate generators cannot confer trust; source-level checker theorems and
   their kernel reductions are the evidence.
5. Write the final P6 review and honest checkpoint only after all the above
   succeed. P6 completion is **not** the full original section-15 goal: the
   general odd-power parameter theorem and the other three manuscript numeric
   bounds remain P7 obligations unless independently completed and checked.
