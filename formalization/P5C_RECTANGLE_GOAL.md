# P5-C: finite rectangle comparison and infinite horizontal representation

Authorized by the user on 29 October 2026 after accepted P5-B. Read
P3B_MEMORY_BOUNDED_GOAL.md and P5B_REVIEW_2026-10-29.md first.

## Acceptance

1. Prove the actual exponential meromorphic kernel's rectangular boundary
   integral equals the accepted finite pole-circle contour, with explicit
   hypotheses placing all poles strictly inside and excluding boundary zeros.
2. Derive this finite comparison from proved complex analysis, not from a
   newly assumed residue/deformation statement. Track high pole orders and
   the positive boundary orientation bottom + right - top - left.
3. With n fixed, let the real truncation tend to infinity. Use accepted
   weighted horizontal integrability and vanishing vertical sides, and prove
   the actual remainder equals the correctly normalized difference of full
   lower/upper horizontal integrals. The affine change of variable must
   produce Jacobian n, not 1/n.
4. Instantiate every actual row of the 17-interval family at positive scale.
   Integrate, build serially under the guard, execute fresh new/regression
   axiom audits and verify source/provenance preservation before acceptance.

## Main mathematical difficulty

The pinned library has centered higher Cauchy formulas and a zero-integral
rectangle theorem for holomorphic functions, but no ready-made rectangular
residue/deformation interface. A possible direct bridge is:

- Compute the rectangle integral of a simple inverse pole using compatible
  logarithm primitives on the four sides; prove the exact 2*pi*i jump.
- Higher inverse powers have global primitives off the pole and integrate
  to zero on the rectangle. Use the same accepted circle power integrals.
- Apply entire divided differences (dslope) recursively to an entire
  numerator, reducing higher poles to the simple pole and holomorphic terms.
- Apply the accepted actual partial fractions, then compare both contours
  by finite linearity. No factorial normalization may be duplicated.

Equivalent fully proved approaches are allowed. An unproved global contour
comparison supplied as an input does not count as completion.

## Ownership and unchanged resources

Main owns finite rectangle geometry/analysis, all compiler access, integration
and acceptance. The already authorized helper conversation
“完成 Lean 4 无理测度形式化” (01a17997-9b46-7911-ba91-8e5af3e3a990) owns only
Analysis/HorizontalLineLimits.lean and P5C_HELPER_HANDOFF.md: affine horizontal
change of variables, integrability and truncation limits. It must not compile,
run generators, restore an old goal or modify any accepted source/root/cache.

All Lean runs use scripts/bounded_lean.py: 6144 MiB job, 2048 MiB Lean,
one worker, <=300 seconds, >=2560 MiB free RAM and >=12288 MiB free commit
before launch. Never overlap compilers or source generators with proof runs.
Preserve v4.35.0, manifest, accepted P1–P5-B sources/caches, D: storage,
C: junctions and paging settings. Do not revive the obsolete blocked task.

Coefficient heights, central asymptotics, sharp gamma and final numerical
irrationality bounds remain later stages.


## Final acceptance

Completed and accepted on 29 October 2026. See P5C_REVIEW_2026-10-29.md and
OddPiPowers/logs/p5c-acceptance-2026-10-29.json. The restrictions above remain
the reproducibility contract; the original full formalization is incomplete.
