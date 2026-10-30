# P6 accepted checkpoint

P6 is complete and accepted on 30 October 2026. The assigned target was the
unconditional pi-cube result strictly below 1203973/1000; it is achieved.
No P6 mathematical, build, audit or acceptance obligation remains.

Read P6_REVIEW_2026-10-30.md for the English mathematical account and
OddPiPowers/logs/p6-acceptance-2026-10-30.json for executed acceptance evidence.
P6_PROGRESS_HISTORY_2026-10-30.md preserves the preceding runtime notes.
Those historical active/running/draft instructions are no longer current.

## Accepted result

OddPiPowers.pi_cube_exponentUpperBound_42170551935_div_35026168 proves

    ExponentUpperBound (Real.pi ^ 3) (42170551935 / 35026168).

The exact exponent is approximately 1203.97275360, strictly below 1203.973.
The fixed theorem has no auxiliary-family, analytic, prime-rate or numerical
hypothesis. The strict witness and Mathlib not-LiouvilleWith corollary are
also accepted. Final source: OddPiPowers/Transfer/TwelveLayerPiCube.lean.
Parameters: s=11, M=187, m=186, L=69, Y=2113/20,
gamma=4543599/100000, D=651297284/10^6, G=255596306/10^6.

## Executed verification

- 264 project modules, 100 new modules and a fresh complete root.
- Final run 20261030T095501: 78 executed targets, 186 verified records.
  The verified records contain 163 prior accepted modules and 23 successful
  new targets from the earlier resource-interrupted run. Across both runs,
  all 100 new modules and the complete root were actually built.
- Root log: logs/p6-lake-OddPiPowers-20261030T095501.log,
  Built OddPiPowers, Build completed successfully (4123 jobs).
- logs/p6-post-build-axioms.log: exact 424 new declarations, exit 0,
  peak 4664.41 MiB, with four compiled final signature checks.
- logs/p6-post-build-regression-axioms.log: exact 602 prior declarations,
  exit 0, peak 5154.42 MiB.
- Only propext, Classical.choice and Quot.sound occur. All 163 previous
  mathematical sources, pinned toolchain/manifest and PNT/Stirling provenance
  passed verification. The verifier returned status=accepted.

No compiler remains running. All compiler access used bounded_lean.py:
6144 MiB aggregate job, 2048 MiB Lean, one worker, at most 300 seconds;
launch gates 2560 MiB free physical RAM and 12288 MiB free commit.
No paging, cache clearing, toolchain, manifest or storage changes occurred.
The identified restarted Overlay/TTS processes were stopped under existing
user authorization when needed to restore the launch threshold.

## Scope after P6

General actual-family heights and Gaussian quotient assembly are reusable
proved interfaces. General odd-power applications and the other manuscript
numeric examples remain P7 and require a later assignment. Do not revive
obsolete P2/P3 or helper goals, or rerun P6 as unfinished. The helper has
completed all assigned drafts and its read-only final checklist.
