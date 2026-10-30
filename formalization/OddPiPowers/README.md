# Odd powers of pi: accepted Lean formalization

**P1–P6 are accepted as of 30 October 2026.** The fixed unconditional theorem
`OddPiPowers.pi_cube_exponentUpperBound_42170551935_div_35026168` proves

```lean
ExponentUpperBound (Real.pi ^ 3) (42170551935 / 35026168)
```

The exponent is approximately 1203.97275360, strictly below 1203.973.
The final source is
[`OddPiPowers/Transfer/TwelveLayerPiCube.lean`](OddPiPowers/Transfer/TwelveLayerPiCube.lean).
Read the [current checkpoint](../P6_CURRENT_CHECKPOINT.md),
[P6 review](../P6_REVIEW_2026-10-30.md), and
[executed acceptance report](logs/p6-acceptance-2026-10-30.json) for the exact
claim and validation evidence. The workspace [README](../../README.md)
describes the manuscripts, experiments and limits of the formalization claim.

The actual integral construction, Gaussian quotient rows, determinant,
coefficient heights, central rates, sharp common-divisor rate and fixed
numerical transfer are proved. The accepted build and axiom audits cover
264 project library modules and use only `propext`, `Classical.choice` and
`Quot.sound`. Draft and scratch results require their own acceptance.

Lean and Mathlib are pinned to `v4.35.0`; retain `lean-toolchain` and
`lake-manifest.json`. The needed proved PNT/Stirling subset is included with
provenance. Earlier candidate-dependency and incomplete-construction notes
in historical records do not override the current accepted checkpoint.

Use the resource contract in the workspace `AGENTS.md`. From the workspace
root a single-file check, after restoring its compiled dependencies, is:

```powershell
python scripts/bounded_lean.py OddPiPowers/Transfer/TwelveLayerPiCube.lean --timeout 300 --log logs/recheck-final.log
```

All Lean trials must go through that runner: one worker, 2048 MiB Lean,
6144 MiB aggregate job, at most 300 seconds, and the documented free-memory
startup gates. The serialized build utility is
`scripts/guarded_library_build.py` at workspace root. Preserve caches and do
not run raw Lean/Lake builds, parallel proof processes or broad recovery
rebuilds. Downloaded dependencies and build caches are not part of the
GitHub source snapshot.

The cofactor-transfer improvement, new numerical shapes and general
odd-power numerical applications remain later work. The repository does
not claim formal acceptance of those stronger targets.
