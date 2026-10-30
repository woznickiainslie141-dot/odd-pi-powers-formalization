# P4: certified prime-product rates (28 October 2026)

The user explicitly authorized P4 after accepted P3-B, and one Luna for
independent elementary work. This supersedes P3-B's stopping boundary only;
all its memory and trust restrictions remain in force.

## Outcome and acceptance

1. Establish unconditional, kernel-audited theta and psi PNT interfaces from
   the pinned v4.35-compatible source. Prove the natural-index log-lcm limit
   using psi, not theta. No assumed PNT parameter counts as completion.
2. Prove weighted prime-window logarithm limits for a fixed finite collection
   of strictly interior cells and fixed finite periods. Normalize by n=L*N.
3. Prove that, eventually, selected primes satisfy p<=L*N<(p*p), and their
   weighted contributions are bounded by the accepted carry certificate.
   Transfer the logarithmic estimate to the actual coefficient divisor.
4. Obtain an eventual exp((gammaLower-eta)*n) lower bound for every eta>0,
   with a general finite-window interface and a positive rational example.
   The example uses the cell (1/69,1/68), weight 6, interior endpoints
   3/206 and 3/205, giving the normalized rate 2/69. It is a calibration,
   not a claim that the full 1180-cell rate equals this much weaker number.
5. Integrate the modules and execute fresh transitive axiom audits. Preserve
   the completed P3-B acceptance records and pinned dependency manifest.

## Proof choices and difficult details

- Strictly shrink each open cell before applying PNT. The prime window
  N/(r+b') < p <= N/(r+a') maps to r+a' <= N/p < r+b', wholly inside
  the original open cell. This avoids charging endpoint primes twice.
- The finite windows must be disjoint, or have an explicit pointwise sum
  certificate. Individual lower bounds cannot simply be summed.
- Fix the number of periods before taking N to infinity. Positivity allows
  a one-sided estimate without exchanging PNT and an infinite sum.
- Small primes below sqrt(L*N) are excluded in the actual divisor. For
  finitely many windows their reciprocal upper endpoints are fixed, so
  all selected primes are eventually above that threshold.
- Theta gives log prime products; psi gives log lcm. Conflating them loses
  prime powers. Use the exact Mathlib psi/log-lcm identity.
- The candidate upstream Wiener source contains two unfinished, apparently
  unused lemmas. Vendor only the needed proof closure, omit that entire
  unused branch and documentation-only Architect metadata, preserve license,
  revision, source hashes and a reproducible adaptation script. Compilation
  and transitive axiom checks, rather than textual non-use, decide acceptance.

## Ownership and execution

Luna owns only Arithmetic/FinitePeriodKernel.lean and drafts elementary
reciprocal-gap identities, order lemmas and exact calibration. Main owns
compiler access, PNT trust, prime windows, divisor bridge and integration.
No simultaneous Lean processes; no overlapping generator and proof runs.
All compiler invocations use scripts/bounded_lean.py, with unchanged limits:
6144 MiB job, 2048 MiB Lean, one thread, <=300 seconds per trial.
Do not revive the old blocked P3-B app task or change paging settings.

## Scope boundary

P5 contour/height estimates, infinite-period sharp evaluation and final
numerical irrationality-measure bounds remain later work. A finite-period
lower bound must state its precision loss; it is not a proof of the earlier
proposed sharp numerical bound.
