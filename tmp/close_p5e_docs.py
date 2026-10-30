"""Close the bounded central-rate and rational certificate-soundness records."""
from pathlib import Path
import json
import re

workspace=Path(__file__).resolve().parents[1]
formal=workspace/'formalization'
project=formal/'OddPiPowers'
data=json.loads((project/'logs/p5e-acceptance-2026-10-29.json').read_text())
assert data['status']=='accepted' and [a['count'] for a in data['audits']]==[50,471]
state=json.loads((project/'logs/p5e-guarded-library-build-state.json').read_text())
rootlog=state['completed'][-1]['log']
match=re.search(r'Build completed successfully \((\d+) jobs\)',(project/rootlog).read_text(encoding='utf-8'))
assert match
rootjobs=match.group(1)
peak=max(a['job']['peak_job_MiB'] for a in data['audits'])
run=data['build_run']
summary=f'''P1 through P5-D and P5-E are accepted. The actual central Stirling/Riemann
rate is now proved, including endpoints, common normalization and uniform
actual/reduced-row exponential bounds for every fixed Y>1/2. The seventeen
base rows are instantiated. Generic fixed integer endpoint families are
also covered. P6-A rational certificate soundness is accepted, retaining
the full AuxiliaryFamily explicitly as a hypothesis.

Complete validation: 151 modules, {data['executed_build_targets']} executed
targets and {data['verified_cached_modules']} verified records, fresh complete
root ({rootjobs} jobs), 50 new and 471 prior axiom checks. Only propext,
Classical.choice and Quot.sound occur. Fresh audit peak {peak:.2f} MiB under
the unchanged 6144 MiB cap. All 139 prior mathematical sources are unchanged.
See formalization/P5E_REVIEW_2026-10-29.md and
formalization/P5E_CURRENT_CHECKPOINT.md (workspace-relative paths).

P6 is not numerically closed. For the fastest first closed instance, use
the balanced all-pole family, unreduced coefficients and a fixed rational
height; its height proof avoids regular factors and improved gamma.
For the manuscript target: explicit s=11, M=187 actual family and
grouping for the pi^3 target; uniform coefficient heights and disk/difference
bounds; complete actual AuxiliaryFamily; sharp divisor rate and kernel-checked
pi/log/atan numeric certificates. The exact height APIs are recorded in
formalization/P5_HEIGHT_PROOF_PLAN.md. Optimal-height existence/uniqueness
is not a prerequisite.
'''
review=f'''# P5-E review — 29 October 2026

Status: **accepted**, including the bounded P6-A certificate-soundness bridge.

## Mathematical implementation

| Requirement | Concrete proof |
|---|---|
| Quantitative Riemann error | GridIntegralBound bounds the left-endpoint sum error by K*delta^2*(u-l), from complete cell integrals. |
| Central integrand | CentralLogLipschitz proves the derivative u/(u^2+Y^2), its global bound 1/Y and the global mean-value inequality for every Y>0. |
| Actual grid and endpoints | ScaledGridLimit treats Ico(aN,bN) and Icc(aN,bN), proving the extra endpoint contributes zero to the normalized limit. |
| Factorial limit | StirlingLogCore is the pinned Mathlib Part 1 positive-limit proof, relocated into OddPiPowers.StirlingLogCore. FactorialLogRate proves the normalized logarithmic limit and fixed integer scaling. |
| One symmetric interval | ScaledIntervalRate combines factorial, Riemann and extra log(n)/n terms to obtain -F_c(Y), using the accepted closed integral. |
| Actual family sum | ActualCentralRate identifies the actual center logarithm as an exact sum over actual intervals and proves its limit for n=L*N,left_a=A_a*N. No analytic limit is assumed. |
| Common normalization | CommonScaleRate uses the accepted unconditional log-lcm theorem to prove log S/n tends to M-1. |
| Actual remainder rates | CentralRemainderRate combines the exact P5-D bound and new limits, then converts the scalar log limit to an exponential inequality uniform over all rows. |
| Seventeen base rows and divisor | TwelveLayerCentralRate instantiates every row, adds any proved actual divisor rate, and supplies the unconditional 2/69 calibration instance. |
| P6 certificate soundness | RationalRateCertificate proves positive-gap monotonicity under d<=D,0<=G<=g, rational cross-comparison soundness and connection to P1 with AuxiliaryFamily explicit. |

For c_a=(L-2*A_a)/L>0 the actual center limit is

    centralLogRatio(Y)/(L*N) -> -sum_a F_(c_a)(Y).

The positive finite central bound has logarithmic rate

    M-1+|theta|*Y-sum_a F_(c_a)(Y).

For every eta>0, eventually all admissible actual rows at i satisfy
norm(row)<=exp((-D0(Y)+eta)*L*N), where
D0=sum_a F_(c_a)(Y)-(pi/2)*Y-(M-1). A certified actual divisor rate gamma
gives the actual quotient rate D0+gamma, with arbitrary positive slack.
All seventeen s=1 rows are instantiated; gamma=2/69 is only weak calibration.
See P5E_MATHEMATICAL_NOTES.md for the detailed finite and limiting calculations.

## Exact scope and P6 entry

The central limiting-rate obligation is closed. The coefficient-height
obligation is open. The manuscript's pi^3 target uses s=11, M=187,m=186,
so its explicit scaled actual family/grouping remains an assembly task.
The P6-A bridge validates the rational rounding direction, denominator
positivity and strict final comparison; its transfer theorem deliberately
keeps the full AuxiliaryFamily hypothesis. No concrete final exponent,
complete actual AuxiliaryFamily, sharp gamma or pi/log/atan numeric
certificate is claimed. Full P6 and the general odd-power P7 remain open.

## Executed verification

The following log paths are relative to formalization/OddPiPowers/.

- logs/p5e-acceptance-2026-10-29.json: exact source freeze, audits,
  prior source preservation and pinned Stirling/PNT provenance passed.
- logs/p5e-guarded-library-build-state.json: completed run {run},
  151 modules, {data['executed_build_targets']} executed targets and
  {data['verified_cached_modules']} verified source-identical records.
- {rootlog}: fresh full root, {rootjobs} jobs, exit 0;
  peak new build {data['peak_build_job_MiB']:.2f} MiB.
- logs/p5e-post-build-axioms.log: 50 new declarations, exit 0.
- logs/p5e-post-build-regression-axioms.log: 471 prior declarations, exit 0.
  Fresh audit peak {peak:.2f} MiB.

Both axiom unions contain only propext, Classical.choice and Quot.sound.
All 139 prior mathematical module hashes and the saved accepted P5-D root
match. Toolchain v4.35.0, manifest and 19 PNT source hashes are unchanged.
The Stirling subset has original/adapted hashes and is reproduced exactly
by scripts/vendor_stirling_log_core.py, including its original copyright
and Apache-2.0 license notice. Namespace relocation avoids collisions with
Mathlib. No missing dependency was built outside the bounded project runner.

Every compiler used bounded_lean.py: 6144 MiB aggregate job, 2048 MiB Lean,
one worker, <=300 seconds, unchanged physical/commit thresholds. No parallel
compiler/generator, cache clearing, paging adjustment, storage move or new
process closure occurred during this round. Earlier failed proof trials are
retained as diagnostics; acceptance uses the final source hashes and jobs.

The already authorized helper drafted FactorialLogRate.lean without a
compiler or generator; main repaired the draft, integrated the pinned core,
compiled and audited it. The helper also wrote the unproved height plan in
P5_HEIGHT_PROOF_PLAN.md. This plan is not an accepted height theorem.
'''
(formal/'P5E_REVIEW_2026-10-29.md').write_text(review,encoding='utf-8')
(formal/'P5E_CURRENT_CHECKPOINT.md').write_text('''# P5-E accepted checkpoint

P5-E and the bounded P6-A certificate-soundness bridge are accepted.
Read P5E_REVIEW_2026-10-29.md and P5E_MATHEMATICAL_NOTES.md.
No compiler remains running. The current assigned bounded work is complete.

'''+summary+'''
All future Lean operations retain the mandatory memory contract. Main alone
owns compiler access. Preserve sources, v4.35.0, manifest, caches, D: storage,
C: junctions and paging settings. The helper has no compiler authority.
''',encoding='utf-8')
(formal/'P6A_REVIEW_2026-10-29.md').write_text('''# P6-A review: rational certificate soundness

Accepted as a bounded infrastructure result, not numerical closure.
Transfer/RationalRateCertificate.lean proves four declarations: positive gap
from one-sided bounds, monotonicity of the exponent ratio, rational strict
cross-comparison soundness, and P1 transfer with an upper bound strictly below
the rational target. The actual AuxiliaryFamily remains an explicit input.

The shared P5-E acceptance covers all four declarations among 50 new checks,
plus 471 regression checks and a full 151-module root build. Only the usual
three foundational axioms occur. See P5E_REVIEW_2026-10-29.md.

The pi^3 s=11 actual family/grouping, uniform heights, complete family,
sharp divisor rate and numeric certificates remain open. No final numerical
irrationality measure is claimed.

Fast first-instance route: balanced all-pole family with unreduced rows,
fixed rational height and a coarse certified target; then extend to the
full s=11 arithmetic/height construction for the intended improvement.
''',encoding='utf-8')
for filename in ['P5E_CENTRAL_RATE_GOAL.md','P6A_CERTIFICATE_GOAL.md']:
    with (formal/filename).open('a',encoding='utf-8') as f:
        f.write('\n## Acceptance\n\nCompleted and accepted on 29 October 2026 within the exact bounded scope. '
                'See P5E_REVIEW_2026-10-29.md and P6A_REVIEW_2026-10-29.md. '
                'Full P6 numerical closure remains open.\n')
with (formal/'P5E_HELPER_HANDOFF.md').open('a',encoding='utf-8') as f:
    f.write('\n## Main acceptance\n\nMain repaired composition and limit normalization, '
            'the logarithmic identity simplification, and the fixed-scaling proof. '
            'The missing full Stirling cache was avoided using a source-reproduced '
            'pinned positive-limit core in a project namespace. All final factorial '
            'declarations are compiled and included in the 50-entry new audit. '
            'The earlier draft caveats are historical; the height plan remains unproved.\n')
docs=project/'docs'
status=docs/'STATUS.md'
old=status.read_text(encoding='utf-8')
tail=old[old.index('The original full goal is not complete.'):]
status.write_text('# Status — P5-E and P6-A soundness accepted, 29 October 2026\n\n'+summary+'\n'+tail,encoding='utf-8')
for filename in ['BLUEPRINT.md','PROOF_GAPS.md','LIBRARY_AUDIT.md','TRUST.md','LUNA_HANDOFF.md']:
    p=docs/filename
    text=p.read_text(encoding='utf-8').replace('## Current P5-D acceptance','## Historical P5-D acceptance')
    text=text.replace('| §4 | Uniform coefficient height and central Stirling/Riemann rate | open |',
        '| §4 | Uniform coefficient height | open |\n| §4 | Actual central Stirling/Riemann rate and uniform row remainder exponent | proved; P5-E accepted |\n| P6 | Rational rate-certificate soundness with explicit AuxiliaryFamily input | proved; bounded P6-A accepted, full numerical instance open |')
    first,rest=text.split('\n',1)
    p.write_text(first+'\n\n## Current P5-E and P6-A acceptance\n\n'+summary+
        '\nEarlier stage records below are historical; their older open lists do not override this checkpoint.\n'+rest,encoding='utf-8')
agent='''# Current work and resource contract

Read `formalization/P3B_MEMORY_BOUNDED_GOAL.md` first, including after context
compaction. P1 through P5-D, P5-E and bounded P6-A certificate soundness are
accepted. Read `formalization/P5E_REVIEW_2026-10-29.md`,
`formalization/P5E_CURRENT_CHECKPOINT.md` and
`formalization/P6A_REVIEW_2026-10-29.md`.
The current bounded work is complete. Full P6 numerical closure is open:
explicit s=11/M=187 actual family and grouping, uniform coefficient heights,
complete AuxiliaryFamily, sharp gamma and numeric pi/log/atan certificates
remain. The unproved height plan is formalization/P5_HEIGHT_PROOF_PLAN.md.
The quickest first closed instance may use the balanced all-pole family
with unreduced rows, avoiding regular factors and improved gamma initially.
Old P2-only launch messages are historical.

All Lean proof trials must use `scripts/bounded_lean.py`: one process tree,
6144 MiB aggregate job cap, Lean 2048 MiB cap, one worker, <=300 seconds.
Launch requires >=2560 MiB free physical memory and >=12288 MiB free commit.
Never bypass the runner, raise limits, use raw Lean/Lake or overlap a
generator and compiler. Split failing proofs/modules. Do not run broad
rebuilds as a first recovery check. Main alone owns compiler access.

Preserve v4.35.0, manifest, source and caches. No new mathematical axioms,
sorry or native-evaluation axioms in accepted results. Draft/table claims
require their own actual build and transitive axiom audit.

Actual storage is `D:\\codex\\pi-irrationality`; old C: content paths are
compatibility junctions. Never recursively remove the junction paths or
change paging settings. Do not revive the obsolete blocked task. The helper
drafted FactorialLogRate and a height plan without compiler or generator;
main repaired, compiled and accepted the factorial result. The height plan
is not a theorem. Never run parallel proof processes.
'''
(workspace/'AGENTS.md').write_text(agent,encoding='utf-8')
Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md').write_text(agent,encoding='utf-8')
print('Accepted P5-E/P6-A docs and both AGENTS copies updated; Lean sources untouched.')
