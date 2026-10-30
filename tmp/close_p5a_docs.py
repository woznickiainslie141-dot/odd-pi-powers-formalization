from pathlib import Path
import json

root = Path(r'D:\codex\pi-irrationality')
formal = root / 'formalization'
docs = formal / 'OddPiPowers/docs'
record = json.loads((formal / 'OddPiPowers/logs/p5a-acceptance-2026-10-29.json').read_text(encoding='utf-8'))
assert record['status'] == 'accepted'
peak = max(a['job']['peak_job_MiB'] for a in record['audits'])

def replace(path, old, new):
    text = path.read_text(encoding='utf-8')
    if old not in text:
        raise RuntimeError((path, old))
    path.write_text(text.replace(old, new), encoding='utf-8')

review = formal / 'P5A_REVIEW_2026-10-29.md'
replace(review, 'Status: **source checks passed; final build and audits pending**.\nDo not interpret this review as acceptance until the recorded gates pass.',
'''Status: **accepted**. The complete guarded dependency validation, both fresh
post-build audits and the machine-readable acceptance verifier passed.''')
replace(review, 'Seven source checks passed under the unchanged guard. Full 111-module dependency validation and fresh 55-new/239-regression audits are pending below.',
'All seven source checks, the complete 111-module dependency validation and fresh audits of 55 new plus 239 prior declarations passed. Only the usual three foundational axioms occur.')
replace(review, 'Pending final guarded build and audits. Every source check used the unchanged',
f'''Final evidence:

- `OddPiPowers/logs/p5a-acceptance-2026-10-29.json`: accepted; all current
  source hashes, vendor provenance, manifest and exact audit name sets checked.
- `OddPiPowers/logs/p5a-guarded-library-build-state.json`: completed run
  {record['build_run']}; 111 dependency modules, 8 executed targets and
  103 source-identical verified P4 records reused.
- `OddPiPowers/logs/p5a-lake-OddPiPowers-{record['build_run']}.log`: fresh
  full root build, 3970 jobs, exit 0. Peak new build job: {record['peak_build_job_MiB']} MiB.
- `OddPiPowers/logs/p5a-post-build-axioms.log`: all 55 new declarations,
  exit 0, peak {record['audits'][0]['job']['peak_job_MiB']} MiB.
- `OddPiPowers/logs/p5a-post-build-regression-axioms.log`: all 239 prior
  declarations, exit 0, peak {record['audits'][1]['job']['peak_job_MiB']} MiB.

The exact union in both audits is propext, Classical.choice and Quot.sound.
No new mathematical axiom, unfinished declaration or native-evaluation axiom
occurs. All 103 previously accepted mathematical source hashes and the saved
P4 root match their accepted ledger. Toolchain and manifest are unchanged.

Every source check used the unchanged''')
replace(review, 'the final verifier will check its\nhash and all 103 unchanged mathematical modules against the P4 build ledger.',
'the final verifier checked its\nhash and all 103 unchanged mathematical modules against the P4 build ledger.')

(formal / 'P5A_CURRENT_CHECKPOINT.md').write_text(f'''# P5-A accepted checkpoint — 29 October 2026

P1, P2, P3-A, P3-B, P4 and P5-A are accepted. See P5A_REVIEW_2026-10-29.md
and OddPiPowers/logs/p5a-acceptance-2026-10-29.json. No compiler is left running.

P5-A closes the actual finite-product horizontal denominator estimate,
nonvanishing on both lines, correct total degree, fixed-degree integrable
majorant on all of R, actual rational-kernel integrability, integral norm
bound and normalized domination uniform in scale and row. The concrete
17-row twelve-layer family is fully instantiated for every positive N.
See P5A_MATHEMATICAL_NOTES.md for detailed computations and scope.

The complete dependency validation passed: 111 modules, 8 executed targets,
103 unchanged verified P4 records reused, and a fresh full root (3970 jobs).
Fresh audits passed all 55 new and 239 prior declarations with only propext,
Classical.choice and Quot.sound. Peak new build: {record['peak_build_job_MiB']} MiB;
peak audit: {peak} MiB. All prior mathematical sources, toolchain and manifest
are preserved. The accepted P4 root is saved as logs/p4-accepted-root.lean.txt.

All proof work still requires scripts/bounded_lean.py: 6144 MiB aggregate job,
2048 MiB Lean, one worker, <=300 seconds, >=2560 MiB free RAM and >=12288 MiB
free commit before launch. Keep D: storage, C: junctions and caches. Do not
change paging settings or revive the obsolete blocked task.

This assigned goal ends at P5-A acceptance. A natural next assignment is the
fixed-n contour/residue representation and vanishing vertical sides, before
height and central-rate limits. Those results, sharp gamma and final numerical
pi-power bounds remain open; do not treat the whole formalization as complete.
''', encoding='utf-8')

status = docs / 'STATUS.md'
t = status.read_text(encoding='utf-8')
end = t.index('The original full goal is not complete.')
t = '''# Status — P5-A accepted, 29 October 2026

P1 through P4 and the assigned P5-A goal are accepted. P5-A closes the actual
horizontal finite-product bound and whole-line integrable kernel domination,
including a single majorant for every positive scale and all 17 actual rows
on both lines. Complete validation: 111 modules, fresh full root (3970 jobs),
55 new plus 239 prior axiom checks, only the usual three foundational axioms.
See ../P5A_REVIEW_2026-10-29.md, ../P5A_CURRENT_CHECKPOINT.md and
logs/p5a-acceptance-2026-10-29.json. P4's earlier evidence is preserved.

The present bounded goal is complete. Contour/residue representation,
coefficient heights, central asymptotics, sharp gamma and final numerical
odd-power bounds remain open. All compiler work retains the existing guard.

''' + t[end:]
t = t.replace('- P5: the full-line paired-factor algebra bound and exact complex norm-square\n  ratio are implemented. Finite-product assembly, integrability, contour\n  deformation, uniform height and central exponential rate remain open.',
'''- P5-A: complete and accepted. Actual denominator reflection, finite-product
  assembly, both-line nonvanishing, exact degree, whole-line majorant and
  actual kernel integrability are proved. The concrete 17-row family has
  uniform normalized domination for every N>=1. The fresh post-build checks
  cover all 55 new declarations; all 239 prior checks also pass.
- Remaining P5: contour/residue representation and vanishing vertical sides,
  coefficient heights, and Stirling/Riemann central rates remain open.''')
t = t.replace('P4 is closed. P5-A is the current authorized goal; the remaining P5 work and\nnumerical/general odd-power applications require further completion.',
'P5-A is closed. Remaining P5 work and numerical/general odd-power\napplications require a later assigned goal and further proof.')
status.write_text(t, encoding='utf-8')
replace(docs / 'BLUEPRINT.md', '| §4 | Height, full finite-product tail, contour opening and central rate | open |',
'''| §4 | Actual full finite-product horizontal tail, both-line nonvanishing, global integrable majorant and uniform 17-row-family domination | proved; P5-A accepted, 111-module validation and 55+239 audits |
| §4 | Coefficient height, contour/residue representation, opening and central rate | open |''')
replace(docs / 'PROOF_GAPS.md', 'The finite product and whole-line integrable majorant are the authorized P5-A\n   target; contour deformation and central asymptotics remain subsequent work.',
'''**P5-A discharged:** actual denominator finite products, exact degree,
   both-line nonvanishing, global integrable majorant and actual kernel
   integrability, with scale/row-uniform concrete 17-row-family domination.
   Contour/residue representation, vertical sides, coefficient heights and
   central asymptotics remain open.''')
replace(docs / 'LIBRARY_AUDIT.md', 'Bridge the specific rational kernel, fixed-n opening and tail limits',
'P5-A closes actual rational-kernel finite products and whole-line integrability; fixed-n contour/residue representation and opening remain open')

handoff = f'''

## P5-A final acceptance — 29 October 2026

The assigned P5-A goal is complete. See ../P5A_REVIEW_2026-10-29.md,
../P5A_MATHEMATICAL_NOTES.md and logs/p5a-acceptance-2026-10-29.json.
The complete 111-module dependency validation passed with 8 executed targets,
103 unchanged verified P4 records and a fresh full root (3970 jobs).
Fresh audits passed exactly 55 new declarations and 239 regression checks;
their axiom union is propext, Classical.choice and Quot.sound. Peak new build
{record['peak_build_job_MiB']} MiB, peak audit {peak} MiB, below the unchanged
6144 MiB job cap. No parallel proof, paging change or cache clearing occurred.

Seven new Analysis modules connect the actual denominator polynomial to the
reflection product, prove nonvanishing and squared norm lower bounds on both
horizontal lines, prove explicit Cauchy domination and integrability, and
bound the actual rational kernel and its integral. The normalized kernel
has a common integrable majorant for all h<=m and d>=2(m+2). The actual
17-row family meets the threshold for every positive N, so its same majorant
is uniform in N, row and line. All 103 old mathematical source hashes and
the saved accepted P4 root match their ledger; manifest/toolchain unchanged.

The next substantive gap is the fixed-n contour/residue representation,
including branches/exponential factor, vertical sides and exact connection
to actual polynomial coefficients. Height and central asymptotics, sharp
gamma and final numerical bounds are also open. P5-A does not accept them.
Do not resume the obsolete blocked task or rerun accepted P2/PNT work.
'''
for filename in ['TRUST.md', 'LUNA_HANDOFF.md']:
    with (docs / filename).open('a', encoding='utf-8') as f:
        f.write(handoff)

agents = (root / 'AGENTS.md').read_text(encoding='utf-8')
agents = agents.replace('The user explicitly authorized P5-A on 29 October;\nread `formalization/P5A_HORIZONTAL_GOAL.md` for its scope and acceptance.\nRemaining P5 work and numerical bounds stay outside this stage.',
'''P5-A is also accepted; read `formalization/P5A_REVIEW_2026-10-29.md` and
`formalization/P5A_CURRENT_CHECKPOINT.md`. The assigned P5-A goal is complete.
Remaining P5 work and numerical bounds require a later assigned goal.''')
for path in [root / 'AGENTS.md', Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md')]:
    path.write_text(agents, encoding='utf-8')
print('P5-A acceptance documents updated; Lean sources unchanged.')
