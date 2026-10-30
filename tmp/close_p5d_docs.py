"""Publish documentation only after the executed P5-D acceptance gate."""
from pathlib import Path
import json
import re

workspace = Path(__file__).resolve().parent.parent
formal = workspace / 'formalization'
project = formal / 'OddPiPowers'
data = json.loads((project / 'logs/p5d-acceptance-2026-10-29.json').read_text())
assert data['status'] == 'accepted'
assert [a['count'] for a in data['audits']] == [42, 429]
assert data['library_modules'] == 140
state = json.loads((project / 'logs/p5d-guarded-library-build-state.json').read_text())
rootlog = state['completed'][-1]['log']
roottext = (project / rootlog).read_text(encoding='utf-8')
match = re.search(r'Build completed successfully \((\d+) jobs\)', roottext)
assert match
rootjobs = match.group(1)
auditpeak = max(a['job']['peak_job_MiB'] for a in data['audits'])
buildpeak = data['peak_build_job_MiB']
run = data['build_run']

review = f'''# P5-D review — 29 October 2026

Status: **accepted**. Complete guarded dependency validation, fresh
post-build new/regression audits and source/provenance verification passed.

## Requirement and concrete proof

| Requirement | Implementation |
|---|---|
| Explicit whole-line constant | HorizontalMajorantIntegral integrates the actual fixed-degree majorant using the exact integral of 1/(1+t^2). Its bound is pi*A, with A independent of scale and row. |
| Both full factorial kernels | WeightedHorizontalIntegral proves both full horizontal integral bounds, including the interval factorial product exactly once. Its norm is the positive real product of interval factorials. |
| Actual central remainder bound | ActualCentralBound combines P5-C with the two explicit line bounds. It proves the 2*pi cancellation, keeps Jacobian n, and bounds n^(h+1) by n^(m+1) uniformly in h<=m. An all-row theorem uses m=M-1. |
| Actual arithmetic quotient | ReducedCentralBound defines the row from the accepted Gaussian quotient matrix, proves D*U_h(z)=sum_j A_hj(i)z^j for all complex z, and divides the bound by the positive actual divisor D. |
| Exact finite center logarithm | CentralLogProducts proves the factorial logarithm and the denominator logarithm using all actual interval occurrences, including endpoints, and an exact formula for log of the positive central bound. |
| Exponential logarithmic interface | ReducedCentralLogBound proves the actual reduced-row inequality with log D subtracted inside the exponential. It assumes no central limiting rate. |
| Concrete construction | TwelveLayerCentralBound applies the bound to all seventeen actual base rows for every N>=1 and Y>1/2. |
| Single-interval calculus | CentralLogIntegral proves the log/sqrt antiderivative, interval integral, zero-width rate, first height derivative and derivative of the explicit first-derivative function. |
| Trust and integration | All eight source modules, complete 140-module dependency validation, 42 new checks and 429 prior regression checks passed. Only the usual three foundational axioms occur. |

## Result

Let S=(M-1)!*lcm(1,...,n)^(M-1), F=product_a length_a!,
B=(Y^2+1/4)^2/(Y^2-1/4), and
A=(Y+3/2)^m*max(1,B)^(m+2). For n>0, Y>1/2,
deg Q>=2(m+2), h<=m and lambda=i*pi/2, the actual row satisfies

    norm(sum_j A_hj(i)*lambda^j)
      <= S*A*n^(m+1)*exp(pi*n*Y/2)*F/norm(Q(-n/2+i*n*Y)).

For the actual integral Gaussian quotient U_h and positive actual divisor D,
the same bound is divided by D. All constants and quantifiers are explicit;
no implicit constant depends on scale or row. The family n=69*N, M=17,
m=16 is instantiated at every positive N.

The exact center logarithm is

    log norm Q_center = d*log n
      + (1/2)*sum_a sum_(r in interval_a) log((r/n-1/2)^2+Y^2).

The interval calculus proves the manuscript's closed integral formula and
F_c'(Y)=2*arctan(c/(2Y)). The derivative of this explicit expression is
-c/(Y^2+c^2/4). The c=0 case is included. See P5D_MATHEMATICAL_NOTES.md.

## Remaining scope

Uniform coefficient heights, the central Stirling/Riemann limiting rates,
existence/uniqueness of an optimal height, sharp arithmetic gamma, general
odd-power parameter closure and final numerical irrationality exponents
remain open. The exact finite logarithmic inequality is not a proof of its
limiting rate. The original whole-project objective remains incomplete.

## Verification and resources

- logs/p5d-acceptance-2026-10-29.json: accepted, exact source hashes,
  audit name sets, prior source preservation and vendor provenance.
- logs/p5d-guarded-library-build-state.json: completed run {run};
  {data['executed_build_targets']} executed targets and
  {data['verified_cached_modules']} source-identical verified records, including
  the 131 P5-C mathematical modules and any successful P5-D checkpoints.
- {rootlog}: fresh complete root, {rootjobs} jobs, exit 0.
  Peak new build {buildpeak:.2f} MiB.
- logs/p5d-post-build-axioms.log: all 42 new checks, exit 0.
- logs/p5d-post-build-regression-axioms.log: all 429 prior checks, exit 0.
  Peak of the fresh audits {auditpeak:.2f} MiB.

Both audits report only propext, Classical.choice and Quot.sound. All 131
prior mathematical module hashes and the saved accepted P5-C root match.
Pinned v4.35.0 toolchain, manifest and all 19 vendored PNT hashes match.
Every compiler uses bounded_lean.py: 6144 MiB job, 2048 MiB Lean, one worker,
<=300 seconds, unchanged physical/commit launch and stop thresholds.

An initial probe and one later build launch were refused by the launch guard
without starting Lean; the successful checkpoint was reused on continuation.
Under the user's process-closing authorization, NVIDIA Overlay, the idle
VBCSCompiler and the Bilibili client were stopped. After memory fluctuations
again reached the launch threshold, the Coopanion local voice application
and its D:/qwen-tts/python/python.exe child were also stopped. Other
applications were retained. No system service,
paging setting, compatibility junction, cache or toolchain was changed.

The existing helper conversation “完成 Lean 4 无理测度形式化” drafted only
CentralLogIntegral.lean and P5D_HELPER_HANDOFF.md. Its handoff explicitly
reports no compiler or generator. Main repaired the pointwise derivative
normalization and log/sqrt continuity, compiled the source and performed
all integration and acceptance operations. The app's wait-status endpoint
returned errors; draft provenance is recorded in the on-disk handoff,
without claiming a verified final conversation status.
'''
(formal / 'P5D_REVIEW_2026-10-29.md').write_text(review, encoding='utf-8')

checkpoint = f'''# P5-D accepted checkpoint — 29 October 2026

P1 through P5-C and P5-D are accepted. The bounded P5-D goal is complete.
Read P5D_REVIEW_2026-10-29.md, P5D_MATHEMATICAL_NOTES.md and
OddPiPowers/logs/p5d-acceptance-2026-10-29.json. No compiler remains running.

P5-D proves the actual central remainder bound with explicit constant A,
including both full horizontal lines, factorial product, common scale,
Jacobian and exact 2*pi cancellation. It is uniform over every row and is
connected to the actual Gaussian coefficient quotient and its positive
actual divisor. All seventeen base-family rows at every N>=1 are included.
The exact finite center logarithm retains every endpoint. The closed-form
single-interval central integral and its height derivative identities pass.

Complete validation: 140 modules, {data['executed_build_targets']} executed
targets and {data['verified_cached_modules']} verified records, including
131 unchanged prior modules, fresh full root ({rootjobs}
jobs), 42 new and 429 prior axiom checks. Only propext, Classical.choice and
Quot.sound occur. Peak new build {buildpeak:.2f} MiB; fresh audit peak
{auditpeak:.2f} MiB. Source/toolchain/manifest/vendor preservation passed.

All Lean access remains through bounded_lean.py with unchanged limits.
Main alone owns compiler access. No parallel proof or generator process.
Keep D: storage, C: compatibility junctions, caches and paging settings.

The next natural assigned goal is actual central Stirling/Riemann limiting
rates, using CentralLogProducts and CentralLogIntegral; uniform coefficient
heights remain a separate substantial obligation. Then sharp gamma,
explicit scaled families/odd-power parameters and final numerical bounds.
P5-D does not instantiate a complete AuxFamily or prove a final exponent.
Do not silently expand this accepted bounded goal.
'''
(formal / 'P5D_CURRENT_CHECKPOINT.md').write_text(checkpoint, encoding='utf-8')

goalpath = formal / 'P5D_CENTRAL_BOUND_GOAL.md'
with goalpath.open('a', encoding='utf-8') as f:
    f.write('\n## Acceptance\n\nCompleted and accepted on 29 October 2026. All eight modules, '
            '140-module dependency validation, 42 new and 429 prior axiom checks passed. '
            'See P5D_REVIEW_2026-10-29.md for the executed evidence and remaining scope.\n')
with (formal / 'P5D_HELPER_HANDOFF.md').open('a', encoding='utf-8') as f:
    f.write('\n## Main integration acceptance\n\nMain repaired pointwise derivative normalization '
            'and explicit log/sqrt continuity. The resulting source and full root compiled '
            'under the bounded runner. P5-D acceptance includes every declaration in this '
            'module among 42 new axiom checks, plus 429 regression checks. Only the usual '
            'three foundational axioms occur. The earlier uncompiled-draft caveats are '
            'historical; see P5D_REVIEW_2026-10-29.md.\n')

summary = f'''P1 through P5-C and P5-D are accepted. The explicit actual central remainder
bound is uniform in row and scale, connected to the actual Gaussian quotient,
and instantiated for all seventeen base rows. Exact finite center logarithms,
the single-interval integral and its height derivatives are proved.
Complete validation: 140 modules ({data['executed_build_targets']} executed,
{data['verified_cached_modules']} verified records, including 131 prior unchanged
modules), fresh full root ({rootjobs} jobs), 42 new and 429
prior axiom checks. Only propext, Classical.choice and Quot.sound occur.
Peak fresh audit {auditpeak:.2f} MiB under the unchanged 6144 MiB cap.
See ../P5D_REVIEW_2026-10-29.md and ../P5D_CURRENT_CHECKPOINT.md.

The bounded goal is complete. Coefficient heights, central Stirling/Riemann
rates, optimal-height theorem, sharp gamma, general odd-power parameters and
final numerical exponents remain open. No complete AuxFamily is claimed.
'''
docs = project / 'docs'
statuspath = docs / 'STATUS.md'
old = statuspath.read_text(encoding='utf-8')
tail = old[old.index('The original full goal is not complete.'):]
statuspath.write_text('# Status — P5-D accepted, 29 October 2026\n\n'+summary+'\n'+tail, encoding='utf-8')
for filename in ['BLUEPRINT.md', 'PROOF_GAPS.md', 'LIBRARY_AUDIT.md', 'TRUST.md', 'LUNA_HANDOFF.md']:
    path = docs / filename
    text = path.read_text(encoding='utf-8')
    first, rest = text.split('\n', 1)
    path.write_text(first+'\n\n## Current P5-D acceptance\n\n'+summary+
        '\nThe following earlier stage records retain their historical scope.\n'+rest, encoding='utf-8')

agent = '''# Current work and resource contract

Read `formalization/P3B_MEMORY_BOUNDED_GOAL.md` first, including after context
compaction. P1, P2, P3-A, P3-B, P4, P5-A, P5-B, P5-C and P5-D are accepted.
Read `formalization/P5D_REVIEW_2026-10-29.md` and
`formalization/P5D_CURRENT_CHECKPOINT.md` for exact scope and evidence.
The bounded P5-D goal is complete. Uniform coefficient heights, central
Stirling/Riemann rates, optimal-height theorem, sharp gamma and final
numerical/general odd-power applications need a later assigned goal.
Old P2-only launch messages are historical.

All Lean proof trials must use `scripts/bounded_lean.py`: one process tree,
6144 MiB aggregate job cap, Lean 2048 MiB cap, one worker, and at most 300 seconds
per trial; launch requires 2560 MiB free physical memory and 12288 MiB free
system commit. Do not bypass the runner, raise its limits, launch raw Lean/Lake
builds, or overlap generators and compiler probes. Split a failing proof or
module instead. Do not run broad rebuilds as a first recovery check.

Preserve toolchain v4.35.0, manifest, source and caches. No new mathematical
axioms, sorry, or native-evaluation axioms in accepted results. Current draft
table proofs are not accepted just because an older root audit passed.

Actual storage is `D:\\codex\\pi-irrationality`. Old C: content directories are
compatibility junctions. Do not recursively remove those junction paths or
change system paging settings. Do not revive the old blocked task while this
chat's goal is running. The existing helper conversation completed its P5-D
CentralLogIntegral draft without compiler or generator; main repaired,
compiled and accepted it. Main alone owns compiler access unless explicitly
handed over. Never run parallel proof processes.
'''
(workspace / 'AGENTS.md').write_text(agent, encoding='utf-8')
compat = Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md')
assert compat.parent.exists()
compat.write_text(agent, encoding='utf-8')
print('P5-D accepted docs and both AGENTS files updated; Lean source untouched.')
