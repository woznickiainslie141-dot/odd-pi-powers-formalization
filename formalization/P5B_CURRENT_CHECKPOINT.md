# P5-B accepted checkpoint — 29 October 2026

P1, P2, P3-A, P3-B, P4, P5-A and P5-B are accepted. The bounded P5-B goal is
complete. Read P5B_REVIEW_2026-10-29.md, P5B_MATHEMATICAL_NOTES.md and
OddPiPowers/logs/p5b-acceptance-2026-10-29.json. No compiler is left running.

P5-B proves the actual partial fractions, disjoint pole-circle geometry and
Cauchy integrals, exact finite contour representation of the actual auxiliary
row at i, weighted horizontal integrability, and both fixed-scale vertical
side limits for the full factorial kernel. The concrete 17-row family is
instantiated. The normalization S and product of interval factorials are
tracked separately and occur exactly once.

Complete dependency validation: 122 modules, 12 executed targets,
110 source-identical verified P5-A records and a fresh full root (3981 jobs).
Fresh audits passed 78 new and 294 prior declarations with only propext,
Classical.choice and Quot.sound. Peak new build 3292.19 MiB;
peak audit 5130.09 MiB. All 110 old mathematical source hashes, the saved
P5-A root, pinned v4.35.0 toolchain and manifest are preserved.

The existing helper conversation “完成 Lean 4 无理测度形式化”
(01a17997-9b46-7911-ba91-8e5af3e3a990) completed only its two assigned drafts
and handoff. It ran no compiler or generator. Main checked/repaired those
drafts and owns all compilation and integration. The helper is idle.

All future Lean access remains through scripts/bounded_lean.py: 6144 MiB job,
2048 MiB Lean, one worker, <=300 seconds; launch at >=2560 MiB free RAM and
>=12288 MiB free commit. Preserve D: storage, C: junctions, caches and paging
settings. Never revive the obsolete blocked P3-B task or replay P2-only work.

Next difficult bridge: compare the finite pole-circle contour with a large
rectangle boundary and then pass horizontal truncations to infinity. P5-B
does NOT establish that contour-deformation equality. Coefficient heights,
central Stirling/Riemann rates, sharp gamma and final numerical odd-power
irrationality bounds also remain open. A later stage needs its own assignment.
