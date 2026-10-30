# P5-A accepted checkpoint — 29 October 2026

P1, P2, P3-A, P3-B, P4 and P5-A are accepted. See P5A_REVIEW_2026-10-29.md
and OddPiPowers/logs/p5a-acceptance-2026-10-29.json. No compiler is left running.

P5-A closes the actual finite-product horizontal denominator estimate,
nonvanishing on both lines, correct total degree, fixed-degree integrable
majorant on all of R, actual rational-kernel integrability, integral norm
bound and normalized domination uniform in scale and row. The concrete
17-row twelve-layer family is fully instantiated for every positive N.
See P5A_MATHEMATICAL_NOTES.md for detailed computations and scope.

The complete dependency validation passed: 111 modules, 8 executed targets,
103 unchanged verified P4 records reused, and a fresh full root (3970 jobs).
Fresh audits passed all 55 new and 239 prior declarations with only propext,
Classical.choice and Quot.sound. Peak new build: 3288.35 MiB;
peak audit: 5126.0 MiB. All prior mathematical sources, toolchain and manifest
are preserved. The accepted P4 root is saved as logs/p4-accepted-root.lean.txt.

All proof work still requires scripts/bounded_lean.py: 6144 MiB aggregate job,
2048 MiB Lean, one worker, <=300 seconds, >=2560 MiB free RAM and >=12288 MiB
free commit before launch. Keep D: storage, C: junctions and caches. Do not
change paging settings or revive the obsolete blocked task.

This assigned goal ends at P5-A acceptance. A natural next assignment is the
fixed-n contour/residue representation and vanishing vertical sides, before
height and central-rate limits. Those results, sharp gamma and final numerical
pi-power bounds remain open; do not treat the whole formalization as complete.
