# P5-B: actual finite contour representation and vertical tails — 29 October 2026

The user authorized the next stage and independent work in another conversation.
P1 through P5-A are accepted; read P5A_REVIEW_2026-10-29.md. The resource
contract in P3B_MEMORY_BOUNDED_GOAL.md remains unchanged.

## Acceptance

1. Derive the actual meromorphic partial-fraction identity by evaluating the
   accepted polynomial numerator identity away from all actual poles. Track
   the product of interval factorials already present in localExpansion.
2. Prove that the actual auxiliary remainder at exp(lambda) equals the
   correctly normalized integral over a finite contour consisting of disjoint
   positively oriented circles about the actual integer poles. Cauchy's higher
   derivative formula, integrability of each summand, finite sum interchange,
   reflection of local indices and the column factorials must all be proved.
   A formal residue sum without an actual contour integral does not suffice.
3. Connect P5-A to the exponential-weighted horizontal kernel, with a norm
   bound independent of the real coordinate, including both lines and all rows.
4. For fixed n and fixed strip height, prove vertical-side integral vanishing
   as its real coordinate tends to +/- infinity, using the actual rational
   denominator and a uniform estimate on the whole finite vertical segment.
   The limit must be taken with n fixed, not jointly with scale growth.
5. Integrate, execute guarded serial and fresh root validation, fresh new and
   regression transitive axiom audits, and source/provenance acceptance checks.

## Difficult details and scope

- Mathlib's higher Cauchy formula in the pinned release is centered at the pole.
  Use disjoint circles of radius less than 1/2; prove that other integer poles
  lie outside their closed balls. A sum of those oriented circles is a genuine
  finite contour surrounding every actual pole once.
- Prove holomorphy and circle integrability before finite integral operations.
  Other principal parts have zero integral in each pole circle; the central
  part gives lambda^j*exp(lambda*(n-ell))/j! with the correct factor 2*pi*i.
- The existing localExpansion includes product(length_a!). Do not multiply
  it twice or incorrectly invert that normalization.
- Nonzero imaginary parts ensure horizontal denominators are nonzero. On
  vertical sides use real-part separation from the fixed finite pole set.
- No assumption that the actual remainder already equals an integral may be
  hidden in a structure or theorem input.

This stage does NOT prove deformation of this finite pole-circle contour to
the two infinite horizontal lines. That equality is the next contour bridge;
vanishing vertical sides and weighted integrability prepare but do not imply
it by themselves. Coefficient heights, central Stirling/Riemann rates, sharp
gamma and final irrationality exponents also remain outside this stage.

## Coordination and resources

Main conversation owns all compiler access. The existing conversation
“完成 Lean 4 无理测度形式化” (01a17997-9b46-7911-ba91-8e5af3e3a990) owns only
drafts Analysis/ContourExponential.lean, Analysis/ActualRemainderAlgebra.lean
and P5B_HELPER_HANDOFF.md. It must not compile, run generators, edit accepted
sources or restore its historical broad goal. Main owns all other new files,
repairs, validation and integration. Do not revive the obsolete blocked P3-B task.

All Lean work uses scripts/bounded_lean.py: 6144 MiB aggregate job, 2048 MiB
Lean, one worker, <=300 seconds, >=2560 MiB free physical RAM and >=12288 MiB
free commit before launch. Never overlap compiler jobs or source generators
with a proof run. Preserve toolchain, manifest, caches, D: storage, C: junctions
and system paging settings. Split a proof/import boundary instead of raising caps.


## Final acceptance

Completed and accepted on 29 October 2026. See P5B_REVIEW_2026-10-29.md and
OddPiPowers/logs/p5b-acceptance-2026-10-29.json. The mathematical scope and
resource restrictions above remain the reproducibility contract.
