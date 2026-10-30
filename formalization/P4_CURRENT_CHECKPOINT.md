# P4 accepted checkpoint — reconciled 29 October 2026

P1, P2, P3-A, P3-B and P4 are accepted. Read P4_REVIEW_2026-10-28.md
for the requirement/evidence table and OddPiPowers/logs/p4-acceptance-2026-10-28.json
for machine-readable verification. Historical resource stops no longer describe
the current proof state. No compiler was left running after acceptance.

P4 proves unconditional audited theta/psi PNT interfaces, the log-lcm rate 1,
fixed finite certified prime-window rates, eventual actual-divisor exponential
lower bounds, integer-weight scaling for supplied grouped realizations, and
the concrete 17-interval family with normalized rate 2/69. This is a small
calibration, not the full table rate or a final bound for a power of pi.

All 104 dependency modules have verified successful build evidence. The final
run executed 25 targets, reused 79 source-identical verified records, and built
the complete root afresh (3963 jobs). Fresh audits passed 67 new checks and
172 regression checks with only propext, Classical.choice and Quot.sound.
Peak final build: 3556.75 MiB; peak final audit: 5105.83 MiB.

Actual storage remains D:\codex\pi-irrationality. Preserve the C: junctions,
v4.35.0 toolchain, manifest, caches and prior acceptance evidence. All compiler
access remains through scripts/bounded_lean.py: 6144 MiB aggregate job cap,
2048 MiB Lean cap, one worker, <=300 seconds; launch requires 2560 MiB free
physical RAM and 12288 MiB free commit. Do not bypass or weaken these checks.

On 29 October the user authorized a new goal. Its bounded scope is P5-A:
actual finite denominator products and whole-line integrable horizontal
majorants. Read P5A_HORIZONTAL_GOAL.md. Full contour deformation, height and
central asymptotics, sharp gamma and final numerical bounds remain later work.
