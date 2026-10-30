from pathlib import Path
import json
import re

root = Path(r'D:\codex\pi-irrationality')
formal = root / 'formalization'
docs = formal / 'OddPiPowers/docs'
record = json.loads((formal / 'OddPiPowers/logs/p5c-acceptance-2026-10-29.json').read_text(encoding='utf-8'))
assert record['status'] == 'accepted'
assert [a['count'] for a in record['audits']] == [57, 372]
peak = max(a['job']['peak_job_MiB'] for a in record['audits'])
root_log = formal / f"OddPiPowers/logs/p5c-lake-OddPiPowers-{record['build_run']}.log"
root_jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)',
    root_log.read_text(encoding='utf-8')).group(1))

def replace(path, old, new):
    text = path.read_text(encoding='utf-8')
    if old not in text:
        if new in text:
            return
        raise RuntimeError((path, old))
    path.write_text(text.replace(old, new), encoding='utf-8')

def append_once(path, heading, body):
    text = path.read_text(encoding='utf-8')
    if heading not in text:
        path.write_text(text + '\n\n' + body, encoding='utf-8')

review = formal / 'P5C_REVIEW_2026-10-29.md'
replace(review, 'Status: **mathematical source checks underway; final build/audits pending**.\nThis draft is not acceptance until the executed final gates are recorded.',
'''Status: **accepted**. Complete guarded dependency validation, fresh
post-build new/regression audits and source/provenance verification passed.''')
replace(review, 'Ten new modules are checked under the existing guard. Final full dependency validation, new/regression axiom audits and source/provenance verification are pending below.',
'All ten source modules, the complete 132-module dependency validation, 57 new checks and 372 prior regression checks passed. Only the usual three foundational axioms occur.')
replace(review, 'Final build/audit evidence is pending. Every proof trial retains the',
f'''Final evidence:

- `OddPiPowers/logs/p5c-acceptance-2026-10-29.json`: accepted, including
  current source hashes, exact audit sets, vendor provenance and manifest.
- `OddPiPowers/logs/p5c-guarded-library-build-state.json`: completed run
  {record['build_run']}; 132 dependency modules, {record['executed_build_targets']} executed targets,
  {record['verified_cached_modules']} unchanged verified P5-B mathematical modules reused.
- `OddPiPowers/logs/p5c-lake-OddPiPowers-{record['build_run']}.log`: fresh
  full root, {root_jobs} jobs, exit 0. Peak new build {record['peak_build_job_MiB']} MiB.
- `OddPiPowers/logs/p5c-post-build-axioms.log`: all 57 new checks,
  exit 0, peak {record['audits'][0]['job']['peak_job_MiB']} MiB.
- `OddPiPowers/logs/p5c-post-build-regression-axioms.log`: all 372 prior
  checks, exit 0, peak {record['audits'][1]['job']['peak_job_MiB']} MiB.

Both audits report only propext, Classical.choice and Quot.sound. No new
mathematical axiom, unfinished declaration or native-evaluation axiom occurs.
All 121 prior mathematical source hashes and the saved accepted P5-B root
match their ledger. Toolchain and manifest are unchanged.

Every proof trial retains the''')

(formal / 'P5C_CURRENT_CHECKPOINT.md').write_text(f'''# P5-C accepted checkpoint — 29 October 2026

P1 through P5-B and P5-C are accepted. The bounded P5-C goal is complete;
read P5C_REVIEW_2026-10-29.md, P5C_MATHEMATICAL_NOTES.md and
OddPiPowers/logs/p5c-acceptance-2026-10-29.json. No compiler remains running.

P5-C proves a finite rectangular Cauchy comparison from explicit logarithm
primitives and entire divided differences, applies it to actual principal
parts, and opens the actual remainder to full lower-minus-upper horizontal
integrals. Fixed n precedes the real truncation limit. Orientation, factorial
normalization and Jacobian n are proved. The actual row at i, its norm
inequality and all seventeen base-family rows at every positive scale are
instantiated. No unproved contour equality is supplied as an assumption.

Complete validation: 132 modules, {record['executed_build_targets']} executed targets,
{record['verified_cached_modules']} source-identical verified P5-B records, fresh full root ({root_jobs} jobs).
Fresh audits passed 57 new and 372 prior checks with only propext,
Classical.choice and Quot.sound. Peak new build {record['peak_build_job_MiB']} MiB;
peak audit {peak} MiB. All 121 prior mathematical sources, saved accepted
P5-B root, pinned v4.35.0 toolchain and manifest are preserved.

The existing helper conversation “完成 Lean 4 无理测度形式化”
(01a17997-9b46-7911-ba91-8e5af3e3a990) drafted only HorizontalLineLimits.lean
and P5C_HELPER_HANDOFF.md. It ran no compiler or generator. Main repaired
one complex-cast simplification, checked the draft and performed every
compiler, integration and acceptance operation. Its drafting is complete.

All later Lean access remains through scripts/bounded_lean.py: 6144 MiB job,
2048 MiB Lean, one worker, <=300 seconds, >=2560 MiB free RAM and >=12288 MiB
free commit before launch. Preserve D: storage, C: junctions, caches and
paging settings. Never revive the obsolete blocked task or replay P2/PNT work.

Next obligations are the uniform coefficient heights and central
Stirling/Riemann exponential rates, followed by sharp gamma, explicit scaled
families/odd-power parameters and final numerical comparisons. This stage
does not complete the whole irrationality-measure formalization. A later
stage requires its own assignment; do not silently expand the closed goal.
''', encoding='utf-8')

status = docs / 'STATUS.md'
text = status.read_text(encoding='utf-8')
end = text.index('The original full goal is not complete.')
text = f'''# Status — P5-C accepted, 29 October 2026

P1 through P5-B and the assigned P5-C goal are accepted. The actual finite
pole-circle contour is now compared to rectangles and opened to two full
horizontal integrals. The exact actual row at i has lower-minus-upper
orientation and Jacobian n, with all seventeen base-family rows instantiated.
Complete validation: 132 modules, fresh full root ({root_jobs} jobs), 57 new
plus 372 prior axiom checks; only the usual three foundational axioms occur.
See ../P5C_REVIEW_2026-10-29.md, ../P5C_CURRENT_CHECKPOINT.md and
logs/p5c-acceptance-2026-10-29.json. Peak audit {peak} MiB under the 6144 MiB cap.

The bounded goal is complete. Uniform coefficient heights, central rates,
sharp gamma, general odd-power parameter closure and final numerical bounds
remain open. The existing single-compiler memory guard is unchanged.

''' + text[end:]
text = text.replace('- Remaining P5: finite pole-circle/rectangle comparison and the infinite\n  horizontal representation, coefficient heights and central rates remain open.',
'''- P5-C: complete and accepted. Finite rectangle/circle comparison, exact
  infinite horizontal representation, Jacobian n and actual seventeen-row
  applications are proved; fresh 57-new/372-regression audits pass.
- Remaining P5: uniform coefficient heights and central Stirling/Riemann
  exponential rates remain open.''')
text = text.replace('P5-B is closed. Remaining contour/analytic work and numerical/general\nodd-power applications require a later assigned goal and further proof.',
'P5-C is closed. Remaining analytic rates and numerical/general odd-power\napplications require a later assigned goal and further proof.')
status.write_text(text, encoding='utf-8')
replace(docs / 'BLUEPRINT.md', '| §4 | Finite circle/rectangle comparison, infinite horizontal representation, coefficient height and central rate | open |',
'''| §4 | Actual rectangle/circle comparison, full lower-minus-upper horizontal representation, Jacobian n and all 17 rows | proved; P5-C accepted, 132-module validation and 57+372 audits |
| §4 | Uniform coefficient height and central Stirling/Riemann rate | open |''')

gaps = docs / 'PROOF_GAPS.md'
text = gaps.read_text(encoding='utf-8')
begin = text.index('P1 through P5-A and P5-B are accepted.')
end = text.index('\n\n1.', begin)
text = text[:begin] + '''P1 through P5-B and P5-C are accepted. Complete dependency validation covers
132 modules and fresh audits of 57 new plus 372 prior checks, with only
propext, Classical.choice and Quot.sound. See ../P5C_REVIEW_2026-10-29.md.
The actual finite-to-infinite contour bridge is closed; the whole original
irrationality-measure formalization remains incomplete.''' + text[end:]
text = text.replace('The finite circle/rectangle\n   comparison, infinite horizontal representation, coefficient heights and\n   central asymptotics remain open.',
'''**P5-C discharged:** finite rectangle/circle comparison and the actual
   infinite horizontal representation, with correct orientation, normalization
   and Jacobian n, including all seventeen actual rows. Coefficient heights
   and central asymptotics remain open.''')
gaps.write_text(text, encoding='utf-8')
replace(docs / 'LIBRARY_AUDIT.md', 'P5-A closes rational finite products and whole-line integrability; P5-B closes finite pole-circle representation and weighted side estimates. Finite circle/rectangle comparison and infinite opening remain open',
'P5-A/P5-B close kernel bounds and finite pole circles; P5-C proves the rectangle comparison and actual infinite horizontal representation. Uniform heights and central rates remain open')
replace(docs / 'LIBRARY_AUDIT.md', '## P5-B contour API decision', '## Historical P5-B contour API decision')
append_once(docs / 'LIBRARY_AUDIT.md', '## P5-C rectangular comparison', '''## P5-C rectangular comparison

The previously missing actual contour comparison is now proved locally.
RectangleLog computes a real simple pole with logarithm primitives and exact
argument jumps. RectangleInversePowers proves the off-pole primitive for
higher inverse powers. Complex.differentiableOn_dslope, from the pinned
RemovableSingularity module, makes the entire divided difference entire;
induction gives rectangle/circle comparison for arbitrary pole order and an
entire numerator. Actual principal sums then give the full finite comparison.
Haar affine change of variables and IntegralEqImproper truncation limits,
with the accepted P5-B vertical estimates, close the full horizontal formula.
No library patch or assumed residue theorem is introduced. All new and
regression axiom closures passed; see the P5-C review and mathematical notes.
''')

handoff = f'''## P5-C final acceptance — 29 October 2026

The assigned P5-C goal is complete. See ../P5C_REVIEW_2026-10-29.md,
../P5C_MATHEMATICAL_NOTES.md and logs/p5c-acceptance-2026-10-29.json.
Complete dependency validation: 132 modules, {record['executed_build_targets']} executed targets,
{record['verified_cached_modules']} unchanged verified P5-B records and a fresh full root ({root_jobs} jobs).
Fresh audits passed exactly 57 new and 372 prior checks, with only propext,
Classical.choice and Quot.sound. Peak new build {record['peak_build_job_MiB']} MiB;
peak audit {peak} MiB, below the unchanged 6144 MiB cap. All 121 prior
mathematical sources and the saved P5-B root match accepted hashes; toolchain
v4.35.0, manifest, vendor provenance and caches are preserved.

Ten new Analysis modules close actual finite rectangle/circle comparison
and full lower-minus-upper horizontal representation. The proof uses exact
logarithm jumps, higher-power primitives and entire dslope induction, then
actual finite principal parts. The Jacobian n and fixed-scale limit order
are proved, with exact actual row-at-i and norm formulas and all seventeen
base-family rows instantiated. No unproved contour equality is an input.

The independent helper drafted only HorizontalLineLimits and its handoff,
without running a compiler or generator. Main repaired, checked, integrated
and audited the draft and all core work. Compiler access stays with main.

Remaining work: uniform coefficient heights and central Stirling/Riemann
exponential rates, sharp gamma arithmetic, explicit scaled families and
general odd-power parameter/numerical closure. P5-C does not accept those
results or the final irrationality bounds. Do not repeat P2/PNT validation,
revive obsolete tasks or weaken the resource guard.
'''
for filename in ['TRUST.md', 'LUNA_HANDOFF.md']:
    append_once(docs / filename, '## P5-C final acceptance — 29 October 2026', handoff)
append_once(formal / 'P5C_HELPER_HANDOFF.md', '## Main integration and acceptance',
'''## Main integration and acceptance

The draft-status warnings above are historical. Main repaired the missing
Complex.ofReal_mul simplification, checked all affine and truncation proofs,
and accepted the final source in the complete P5-C build and fresh axiom
audits. The finite contour bridge was separately proved by main. See
P5C_REVIEW_2026-10-29.md; the helper ran no compiler or generator.
''')
append_once(formal / 'P5C_RECTANGLE_GOAL.md', '## Final acceptance', '''## Final acceptance

Completed and accepted on 29 October 2026. See P5C_REVIEW_2026-10-29.md and
OddPiPowers/logs/p5c-acceptance-2026-10-29.json. The restrictions above remain
the reproducibility contract; the original full formalization is incomplete.
''')

contract_path = root / 'AGENTS.md'
contract = contract_path.read_text(encoding='utf-8')
tail = contract[contract.index('All Lean proof trials must use'):]
contract = '''# Current work and resource contract

Read `formalization/P3B_MEMORY_BOUNDED_GOAL.md` first, including after context
compaction. P1, P2, P3-A, P3-B, P4, P5-A, P5-B and P5-C are accepted. Read
`formalization/P5C_REVIEW_2026-10-29.md` and
`formalization/P5C_CURRENT_CHECKPOINT.md` for exact scope and evidence.
The bounded P5-C goal is complete. Uniform coefficient heights, central
rates, sharp gamma and final numerical/general odd-power applications need
a later assigned goal. Old P2-only launch messages are historical.

''' + tail
contract = contract.replace('The P5-B helper conversation completed its two assigned drafts without\nrunning a compiler or generator.',
'The P5-C helper conversation completed its assigned horizontal-limit draft\nwithout running a compiler or generator.')
for path in [contract_path, Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md')]:
    path.write_text(contract, encoding='utf-8')
print('P5-C acceptance documentation updated; Lean sources unchanged.')
