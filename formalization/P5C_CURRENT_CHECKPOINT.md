# P5-C accepted checkpoint — 29 October 2026

P1 through P5-B and P5-C are accepted. The bounded P5-C goal is complete;
read P5C_REVIEW_2026-10-29.md, P5C_MATHEMATICAL_NOTES.md and
OddPiPowers/logs/p5c-acceptance-2026-10-29.json. No compiler remains running.

P5-C proves a finite rectangular Cauchy comparison from explicit logarithm
primitives and entire divided differences, applies it to actual principal
parts, and opens the actual remainder to full lower-minus-upper horizontal
integrals. Fixed n precedes the real truncation limit. Orientation, factorial
normalization and Jacobian n are proved. The actual row at i, its norm
inequality and all seventeen base-family rows at every positive scale are
instantiated. No unproved contour equality is supplied as an assumption.

Complete validation: 132 modules, 11 executed targets,
121 source-identical verified P5-B records, fresh full root (3991 jobs).
Fresh audits passed 57 new and 372 prior checks with only propext,
Classical.choice and Quot.sound. Peak new build 3294.46 MiB;
peak audit 5135.56 MiB. All 121 prior mathematical sources, saved accepted
P5-B root, pinned v4.35.0 toolchain and manifest are preserved.

The existing helper conversation “完成 Lean 4 无理测度形式化”
(01a17997-9b46-7911-ba91-8e5af3e3a990) drafted only HorizontalLineLimits.lean
and P5C_HELPER_HANDOFF.md. It ran no compiler or generator. Main repaired
one complex-cast simplification, checked the draft and performed every
compiler, integration and acceptance operation. Its drafting is complete.

All later Lean access remains through scripts/bounded_lean.py: 6144 MiB job,
2048 MiB Lean, one worker, <=300 seconds, >=2560 MiB free RAM and >=12288 MiB
free commit before launch. Preserve D: storage, C: junctions, caches and
paging settings. Never revive the obsolete blocked task or replay P2/PNT work.

Next obligations are the uniform coefficient heights and central
Stirling/Riemann exponential rates, followed by sharp gamma, explicit scaled
families/odd-power parameters and final numerical comparisons. This stage
does not complete the whole irrationality-measure formalization. A later
stage requires its own assignment; do not silently expand the closed goal.
