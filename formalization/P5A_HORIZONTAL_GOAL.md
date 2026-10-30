# P5-A: actual horizontal products and integrable tails — 29 October 2026

The user authorized the next goal after P4 acceptance. This stage closes a
specific difficult analytic bridge, rather than asserting all of P5 at once.
Read P3B_MEMORY_BOUNDED_GOAL.md first; its resource contract remains mandatory.
P4_REVIEW_2026-10-28.md and its machine-readable evidence accept P1–P4.

## Acceptance

1. Prove a finite-product consequence of HorizontalPair on the whole real
   horizontal coordinate. Include repeated factors and fixed points of the
   reflection, so even/odd interval lengths and central factors are covered.
2. Connect the bound to ActualIntervals.denominator, using its actual interval
   factors, correct totalMultiplicity, n>0 and Y>1/2. Prove nonvanishing on both
   horizontal lines. A theorem about unrelated surrogate products is insufficient.
3. Derive a fixed-degree majorant for the actual rational kernel z^h/Q(z),
   after the horizontal rescaling z=n*(-1/2+t+iY). Prove the majorant integrable
   on all of R, with a constant independent of n and uniform over finite rows
   h<=m once the denominator degree exceeds a fixed row-dependent threshold.
4. Integrate the modules, execute guarded targeted and root validation, and
   fresh transitive axiom checks for the new results. Preserve accepted P4
   sources, cache evidence, toolchain and manifest. No sorry, new mathematical
   axiom or native-evaluation axiom is permitted.

## Proof design and difficult details

- Reflect every pole r to n-r inside the same actual interval. A product
  reindexing proof covers central factors without silently dropping one factor.
- The scalar inequality bounds the square of a pair ratio. Track norm versus
  normSq and the degree exponent exactly; no factor-of-two shortcut is allowed.
- An involution argument may square the entire finite product, then recover
  the nonnegative inequality. This avoids manually partitioning all parity cases.
- The zero-degree/zero-scale cases must be stated accurately. The horizontal
  denominator is nonzero because its imaginary part is nonzero at every pole.
- An integrable majorant must cover both tails and the compact central interval.
  Pointwise decay or integrability of a candidate unrelated to the actual kernel
  does not close this stage. Uniformity in the row index must be explicit.

## Execution and boundary

Every Lean probe/build uses scripts/bounded_lean.py: 6144 MiB aggregate job,
2048 MiB Lean, one worker, <=300 seconds. Keep the existing 2560 MiB free RAM
and 12288 MiB free commit launch checks. Never overlap compiler processes,
generation and compilation; split heavy files instead of raising limits.
Actual storage is D:\codex\pi-irrationality. Do not change paging settings,
remove C: junctions, clear caches or revive the obsolete blocked task.

Full contour deformation/residue-to-coefficient representation, height rates,
Stirling/Riemann central asymptotics, sharp arithmetic gamma and all final
numerical irrationality bounds remain later stages. This stage supplies the
whole-line domination needed before those limit arguments can be accepted.
