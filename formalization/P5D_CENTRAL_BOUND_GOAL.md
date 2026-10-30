# P5-D: explicit central bounds

Assigned 29 October 2026 after accepted P5-C. Main owns all compiler access.
The existing helper conversation drafts only CentralLogIntegral.lean and
P5D_HELPER_HANDOFF.md; it must not compile or run generators.

## Acceptance boundary

Prove a closed, scale-independent constant for the full horizontal majorant;
derive the actual auxiliary remainder bound including factorial product,
common normalization, denominator at the center, exponential weight and
Jacobian. Make the bound uniform in every admissible row. Connect it to
the actual common-divisor quotient and instantiate all seventeen base rows.
Expose the exact finite logarithmic center product, retaining endpoints.
Check the single-interval central logarithmic integral and its rate-function
calculus, with any unresolved details explicitly recorded.

No coefficient-height theorem, Stirling/Riemann limiting rate, sharp gamma,
general odd-power parameter choice or final numerical exponent is claimed.
Complete root dependency validation, exact new/regression axiom audits,
source preservation and review/checkpoint are required for acceptance.

## Resources

Read P3B_MEMORY_BOUNDED_GOAL.md. All compiler operations use bounded_lean.py:
6144 MiB aggregate job, 2048 MiB Lean, one worker, <=300 seconds per trial,
>=2560 MiB free physical memory and >=12288 MiB free commit at launch.
No parallel compiler/generator, raw Lean/Lake, cap increase or broad recovery
rebuild. Preserve accepted sources, pinned v4.35.0 toolchain, manifest,
caches, D: storage, C: junctions and paging settings.

## Acceptance

Completed and accepted on 29 October 2026. All eight modules, 140-module dependency validation, 42 new and 429 prior axiom checks passed. See P5D_REVIEW_2026-10-29.md for the executed evidence and remaining scope.
