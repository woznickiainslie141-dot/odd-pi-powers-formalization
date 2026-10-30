from pathlib import Path
import json
import re

root = Path(r'D:\codex\pi-irrationality')
formal = root / 'formalization'
docs = formal / 'OddPiPowers/docs'
record = json.loads((formal / 'OddPiPowers/logs/p5b-acceptance-2026-10-29.json').read_text(encoding='utf-8'))
assert record['status'] == 'accepted'
assert [a['count'] for a in record['audits']] == [78, 294]
peak = max(a['job']['peak_job_MiB'] for a in record['audits'])
root_log = formal / f"OddPiPowers/logs/p5b-lake-OddPiPowers-{record['build_run']}.log"
root_jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)',
    root_log.read_text(encoding='utf-8')).group(1))

def replace(path, old, new):
    text = path.read_text(encoding='utf-8')
    if old not in text:
        if new in text:
            return
        raise RuntimeError((path, old))
    path.write_text(text.replace(old, new), encoding='utf-8')

def append_once(path, heading, text):
    content = path.read_text(encoding='utf-8')
    if heading not in content:
        path.write_text(content + '\n\n' + text, encoding='utf-8')

review = formal / 'P5B_REVIEW_2026-10-29.md'
replace(review, 'Status: **source checks passed; final build and audits pending**.\nThe assigned stage is not accepted until the final gates below have passed.',
'''Status: **accepted**. The complete guarded dependency validation, fresh
post-build new/regression audits and source/provenance acceptance verifier passed.''')
replace(review, 'Eleven source modules passed guarded checks. Full 122-module dependency validation, 78 new checks and 294 regression checks are pending below.',
'All eleven source modules, the complete 122-module dependency validation, 78 new checks and 294 regression checks passed. Their axiom union is exactly propext, Classical.choice and Quot.sound.')
replace(review, 'Final guarded build and audits are pending. All trials used the unchanged',
f'''Final evidence:

- `OddPiPowers/logs/p5b-acceptance-2026-10-29.json`: accepted; all current
  source hashes, exact audit sets, vendor provenance and manifest checked.
- `OddPiPowers/logs/p5b-guarded-library-build-state.json`: completed run
  {record['build_run']}; 122 modules, {record['executed_build_targets']} executed targets,
  {record['verified_cached_modules']} unchanged verified P5-A module records reused.
- `OddPiPowers/logs/p5b-lake-OddPiPowers-{record['build_run']}.log`: fresh
  full root build, {root_jobs} jobs, exit 0. Peak new build job {record['peak_build_job_MiB']} MiB.
- `OddPiPowers/logs/p5b-post-build-axioms.log`: all 78 new declarations,
  exit 0, peak {record['audits'][0]['job']['peak_job_MiB']} MiB.
- `OddPiPowers/logs/p5b-post-build-regression-axioms.log`: all 294 prior
  checks, exit 0, peak {record['audits'][1]['job']['peak_job_MiB']} MiB.

Both fresh audits report only propext, Classical.choice and Quot.sound. No
unfinished declaration, new mathematical axiom or native-evaluation axiom
occurs. All 110 prior mathematical sources and the saved P5-A root match
the accepted source hashes. Toolchain and manifest are unchanged.

All trials used the unchanged''')

(formal / 'P5B_CURRENT_CHECKPOINT.md').write_text(f'''# P5-B accepted checkpoint — 29 October 2026

P1, P2, P3-A, P3-B, P4, P5-A and P5-B are accepted. The bounded P5-B goal is
complete. Read P5B_REVIEW_2026-10-29.md, P5B_MATHEMATICAL_NOTES.md and
OddPiPowers/logs/p5b-acceptance-2026-10-29.json. No compiler is left running.

P5-B proves the actual partial fractions, disjoint pole-circle geometry and
Cauchy integrals, exact finite contour representation of the actual auxiliary
row at i, weighted horizontal integrability, and both fixed-scale vertical
side limits for the full factorial kernel. The concrete 17-row family is
instantiated. The normalization S and product of interval factorials are
tracked separately and occur exactly once.

Complete dependency validation: 122 modules, {record['executed_build_targets']} executed targets,
{record['verified_cached_modules']} source-identical verified P5-A records and a fresh full root ({root_jobs} jobs).
Fresh audits passed 78 new and 294 prior declarations with only propext,
Classical.choice and Quot.sound. Peak new build {record['peak_build_job_MiB']} MiB;
peak audit {peak} MiB. All 110 old mathematical source hashes, the saved
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
''', encoding='utf-8')

status = docs / 'STATUS.md'
text = status.read_text(encoding='utf-8')
end = text.index('The original full goal is not complete.')
text = f'''# Status — P5-B accepted, 29 October 2026

P1 through P5-A and the assigned P5-B goal are accepted. P5-B connects the
actual auxiliary remainder at i to genuine finite pole-circle integrals,
proves exponential-weighted horizontal integrability and fixed-n vertical
side vanishing, and instantiates the actual 17-row family.
Complete validation: 122 modules, fresh full root ({root_jobs} jobs), 78 new plus
294 prior axiom checks, only the usual three foundational axioms. See
../P5B_REVIEW_2026-10-29.md, ../P5B_CURRENT_CHECKPOINT.md and
logs/p5b-acceptance-2026-10-29.json. Peak audit {peak} MiB under the 6144 MiB cap.

The current bounded goal is complete. Finite pole-circle/rectangle comparison
and infinite horizontal contour representation, coefficient heights, central
asymptotics, sharp gamma and final numerical odd-power bounds remain open.
The unchanged single-compiler memory guard applies to all later work.

''' + text[end:]
text = text.replace('- Remaining P5: contour/residue representation and vanishing vertical sides,\n  coefficient heights, and Stirling/Riemann central rates remain open.',
'''- P5-B: complete and accepted. Actual finite pole-circle representation,
  weighted horizontal integrability, fixed-scale vertical sides and concrete
  17-row applications are proved; fresh 78-new/294-regression audits pass.
- Remaining P5: finite pole-circle/rectangle comparison and the infinite
  horizontal representation, coefficient heights and central rates remain open.''')
text = text.replace('P5-A is closed. Remaining P5 work and numerical/general odd-power\napplications require a later assigned goal and further proof.',
'P5-B is closed. Remaining contour/analytic work and numerical/general\nodd-power applications require a later assigned goal and further proof.')
status.write_text(text, encoding='utf-8')
replace(docs / 'BLUEPRINT.md', '| §4 | Coefficient height, contour/residue representation, opening and central rate | open |',
'''| §2, §4 | Actual finite pole-circle representation at i, weighted horizontal kernels and fixed-scale vertical-side vanishing; all 17 actual rows | proved; P5-B accepted, 122-module validation and 78+294 audits |
| §4 | Finite circle/rectangle comparison, infinite horizontal representation, coefficient height and central rate | open |''')

gaps = docs / 'PROOF_GAPS.md'
old = gaps.read_text(encoding='utf-8')
begin = old.index('P1, P2, P3-A, P3-B and P4 are now accepted.')
end = old.index('\n\n1.', begin)
old = old[:begin] + '''P1 through P5-A and P5-B are accepted. The latest complete dependency
validation covers 122 modules and fresh audits of 78 new plus 294 prior
declarations, with only propext, Classical.choice and Quot.sound. See
`../P5B_REVIEW_2026-10-29.md`. The full original manuscript goal is incomplete.''' + old[end:]
old = old.replace('The all-pole global partial-fraction identity\n   mentioned in older handoffs is not needed by this P2 proof route and is\n   not claimed proved.',
'''The all-pole partial-fraction identity was not needed by P2; P5-B now
   proves its actual meromorphic evaluation and uses it to derive the finite
   pole-circle integral representation.''')
old = old.replace('Continuous\n   certificates and divisor asymptotics remain separate obligations.',
'Continuous certificates were subsequently accepted in P3-B and finite-window\n   divisor rates in P4; sharp arithmetic gamma remains separate.')
old = old.replace('Contour/residue representation, vertical sides, coefficient heights and\n   central asymptotics remain open.',
'''**P5-B discharged:** actual finite pole-circle representation at i,
   exponential-weighted horizontal integrability and both fixed-scale vertical
   limits, including the actual 17-row family. The finite circle/rectangle
   comparison, infinite horizontal representation, coefficient heights and
   central asymptotics remain open.''')
gaps.write_text(old, encoding='utf-8')
replace(docs / 'LIBRARY_AUDIT.md', 'P5-A closes actual rational-kernel finite products and whole-line integrability; fixed-n contour/residue representation and opening remain open',
'P5-A closes rational finite products and whole-line integrability; P5-B closes finite pole-circle representation and weighted side estimates. Finite circle/rectangle comparison and infinite opening remain open')
append_once(docs / 'LIBRARY_AUDIT.md', '## P5-B contour API decision', '''## P5-B contour API decision

The pinned CauchyIntegral higher-derivative formula is centered at the pole;
its TODO still requests a general interior-point version. P5-B uses radius-1/4
circles centered at each integer pole and proves the other principal parts
holomorphic on those disks. This gives actual finite contour integrals using
the existing Cauchy-Goursat and higher Cauchy formulas, with no residue theorem
assumed. ExpDeriv supplies the iterated exponential derivative. Exact norm
estimates and Bochner/interval integrability give horizontal and vertical bounds.
The finite circle/rectangle comparison is not supplied by these APIs and is
still a substantive remaining contour proof. See the P5-B mathematical notes.
''')

handoff = f'''## P5-B final acceptance — 29 October 2026

The assigned P5-B goal is complete. See ../P5B_REVIEW_2026-10-29.md,
../P5B_MATHEMATICAL_NOTES.md and logs/p5b-acceptance-2026-10-29.json.
Complete dependency validation covers 122 modules, {record['executed_build_targets']} executed targets,
{record['verified_cached_modules']} verified unchanged P5-A records and a fresh full root ({root_jobs} jobs).
Fresh audits passed exactly 78 new and 294 prior declarations, with only
propext, Classical.choice and Quot.sound. Peak new build {record['peak_build_job_MiB']} MiB;
peak audit {peak} MiB under the unchanged 6144 MiB cap. All 110 prior
mathematical source hashes and the saved P5-A root match the accepted ledger.
Toolchain v4.35.0 and manifest remain unchanged.

Eleven new Analysis modules prove actual partial fractions and genuine small
pole-circle integrals, exact actual row normalization at i, both-line
exponential horizontal integrability and both fixed-scale vertical limits
for the full factorial kernel. The actual 17-row family is instantiated.
The independent helper conversation drafted only ContourExponential and
ActualRemainderAlgebra and ran no compiler/generator. Main repaired, checked,
integrated and audited all results. The helper is idle; compiler access
remains exclusively with main under the existing bounded runner.

Next hard bridge: an explicit comparison of the pole-circle contour with a
large rectangle, then horizontal truncation limits. Existing weighted
integrability and vertical limits do not imply that equality by themselves.
After that, coefficient heights and central rates are still required before
the auxiliary family can instantiate the transfer theorem. Sharp gamma and
final numerical pi-power bounds remain open. Do not revive obsolete tasks,
replay P2/PNT checks or weaken the resource guard.
'''
for filename in ['TRUST.md', 'LUNA_HANDOFF.md']:
    append_once(docs / filename, '## P5-B final acceptance — 29 October 2026', handoff)
append_once(formal / 'P5B_HELPER_HANDOFF.md', '## Main integration and acceptance',
'''## Main integration and acceptance

The original draft status above is historical. Main narrowed the broad tactic
import, checked/repaired both files, and accepted their final source in the
complete P5-B build and fresh transitive axiom audits. See
P5B_REVIEW_2026-10-29.md. The helper did not run any compiler or generator.
''')
goal = formal / 'P5B_CONTOUR_GOAL.md'
append_once(goal, '## Final acceptance', '''## Final acceptance

Completed and accepted on 29 October 2026. See P5B_REVIEW_2026-10-29.md and
OddPiPowers/logs/p5b-acceptance-2026-10-29.json. The mathematical scope and
resource restrictions above remain the reproducibility contract.
''')

contract_path = root / 'AGENTS.md'
contract = contract_path.read_text(encoding='utf-8')
tail = contract[contract.index('All Lean proof trials must use'):]
contract = '''# Current work and resource contract

Read `formalization/P3B_MEMORY_BOUNDED_GOAL.md` first, including after context
compaction. P1, P2, P3-A, P3-B, P4, P5-A and P5-B are accepted. Read
`formalization/P5B_REVIEW_2026-10-29.md` and
`formalization/P5B_CURRENT_CHECKPOINT.md` for the latest evidence and exact
scope. The assigned P5-B goal is complete. Finite circle/rectangle comparison,
infinite horizontal representation, remaining analytic rates and numerical
bounds require a later assigned goal. Old P2-only launch text is historical.

''' + tail
contract = contract.replace("The user has now authorized one Luna assistant for\nP4's easier independent lemmas. It may draft its assigned file and inspect\nsources while the main agent works, but only the main agent owns compiler\naccess until explicitly handed over. Never run parallel proof processes.",
'''The P5-B helper conversation completed its two assigned drafts without
running a compiler or generator. Main alone owns compiler access unless
explicitly handed over. Never run parallel proof processes.''')
for path in [contract_path, Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md')]:
    path.write_text(contract, encoding='utf-8')
print('P5-B acceptance documentation updated; Lean sources unchanged.')
