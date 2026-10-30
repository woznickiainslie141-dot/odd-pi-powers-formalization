from pathlib import Path

root = Path(r'D:\codex\pi-irrationality')
formal = root / 'formalization'
docs = formal / 'OddPiPowers/docs'

def replace(path, old, new):
    text = path.read_text(encoding='utf-8')
    if old not in text:
        raise RuntimeError(f'Missing replacement in {path}: {old[:70]}')
    path.write_text(text.replace(old, new), encoding='utf-8')

review = formal / 'P4_REVIEW_2026-10-28.md'
replace(review, 'Status: mathematical modules and root source check passed. The full serial\nLake build and fresh post-build audits are the remaining acceptance gates.\nDo not treat this review draft as acceptance before those gates finish.',
'''Status: **accepted**. The complete guarded dependency validation and fresh
post-build audits passed on 28 October 2026. Documentation was reconciled
with the machine-readable acceptance evidence on 29 October 2026.''')
replace(review, 'Root source check passed: `logs/p4-OddPiPowers-20261028T173102.log`, peak 4582.23 MiB. Complete serial Lake validation remains pending below.',
'Complete 104-module dependency validation passed, including a fresh full root build (3963 jobs). The final run executed 25 targets and reused 79 source-identical targets backed by prior successful guarded records. Peak final-build job commit: 3556.75 MiB.')
replace(review, 'The prepared final verifier checks the full build\'s source hashes, exact audit name sets, standard axiom set and no unfinished declarations. It has not yet established final acceptance.',
'The executed final verifier checked all 104 current source hashes, successful guarded build records, cache provenance, exact audit name sets, the standard axiom set, all 19 vendor hashes and absence of unfinished declarations. It reports accepted.')
replace(review, 'Final machine-readable acceptance record and post-build audit results:\npending the running serial validation.',
'''Final evidence:

- `OddPiPowers/logs/p4-acceptance-2026-10-28.json`: accepted.
- `OddPiPowers/logs/p4-guarded-library-build-state.json`: 104 modules,
  completed run 20261028T174533; 25 executed and 79 verified cached records.
- `OddPiPowers/logs/p4-lake-OddPiPowers-20261028T174533.log`: fresh complete
  root, 3963 jobs, exit 0.
- `OddPiPowers/logs/p4-post-build-axioms.log`: all 67 configured checks,
  exit 0, peak 5105.83 MiB.
- `OddPiPowers/logs/p4-post-build-regression-axioms.log`: all 172 regression
  checks, exit 0, peak 4565.15 MiB.

Both audits report only propext, Classical.choice and Quot.sound. All peaks
remain below the unchanged 6144 MiB cap. The pinned manifest SHA-256 is
e46b8f7bf97f5d4ee8f0b4f5155b71dbead74f1c2aef1b55c34677ffbd9dbf38.
P4 is closed; P5 and final numerical bounds are not accepted by this review.''')

(formal / 'P4_CURRENT_CHECKPOINT.md').write_text('''# P4 accepted checkpoint — reconciled 29 October 2026

P1, P2, P3-A, P3-B and P4 are accepted. Read P4_REVIEW_2026-10-28.md
for the requirement/evidence table and OddPiPowers/logs/p4-acceptance-2026-10-28.json
for machine-readable verification. Historical resource stops no longer describe
the current proof state. No compiler was left running after acceptance.

P4 proves unconditional audited theta/psi PNT interfaces, the log-lcm rate 1,
fixed finite certified prime-window rates, eventual actual-divisor exponential
lower bounds, integer-weight scaling for supplied grouped realizations, and
the concrete 17-interval family with normalized rate 2/69. This is a small
calibration, not the full table rate or a final bound for a power of pi.

All 104 dependency modules have verified successful build evidence. The final
run executed 25 targets, reused 79 source-identical verified records, and built
the complete root afresh (3963 jobs). Fresh audits passed 67 new checks and
172 regression checks with only propext, Classical.choice and Quot.sound.
Peak final build: 3556.75 MiB; peak final audit: 5105.83 MiB.

Actual storage remains D:\\codex\\pi-irrationality. Preserve the C: junctions,
v4.35.0 toolchain, manifest, caches and prior acceptance evidence. All compiler
access remains through scripts/bounded_lean.py: 6144 MiB aggregate job cap,
2048 MiB Lean cap, one worker, <=300 seconds; launch requires 2560 MiB free
physical RAM and 12288 MiB free commit. Do not bypass or weaken these checks.

On 29 October the user authorized a new goal. Its bounded scope is P5-A:
actual finite denominator products and whole-line integrable horizontal
majorants. Read P5A_HORIZONTAL_GOAL.md. Full contour deformation, height and
central asymptotics, sharp gamma and final numerical bounds remain later work.
''', encoding='utf-8')

status = docs / 'STATUS.md'
t = status.read_text(encoding='utf-8')
end = t.index('The original full goal is not complete.')
t = '''# Status — P4 accepted; P5-A authorized, 29 October 2026

P4 passed the complete 104-module dependency validation and fresh audits of
67 new and 172 existing declarations. Only propext, Classical.choice and
Quot.sound occur. See ../P4_REVIEW_2026-10-28.md and
logs/p4-acceptance-2026-10-28.json. P4 includes unconditional PNT, psi/lcm,
general finite-window actual-divisor rates, scaling and concrete rate 2/69.
The latter is a calibration, not a final irrationality-exponent bound.

The user authorized P5-A on 29 October: actual denominator finite products
and an integrable whole-line horizontal majorant. See ../P5A_HORIZONTAL_GOAL.md.
The unchanged bounded runner owns every compiler process; no parallel proofs.

''' + t[end:]
t = t.replace('The project data', 'The project data', 1)
t = t.replace('The candidate prime-number theorem is still not accepted as a\n  dependency; its relevant theorem needs a build and transitive axiom check.',
'The required pinned PNT proof subset is accepted after compilation and\n  executed transitive axiom checks; the full upstream package is not imported.')
t = t.replace('- P4: prime asymptotics and a one-sided divisor exponential rate remain open.',
'- P4: complete and accepted. Unconditional theta/psi limits, log-lcm rate 1,\n  finite-window actual-divisor exponential lower bounds and scaling are proved.\n  Concrete base-family calibration: 2/69. Sharp gamma arithmetic remains open.')
t = t.replace('P3-B is closed. P4/P5 and numerical/general odd-power applications remain\nseparate later goals.',
'P4 is closed. P5-A is the current authorized goal; the remaining P5 work and\nnumerical/general odd-power applications require further completion.')
status.write_text(t, encoding='utf-8')
replace(docs / 'BLUEPRINT.md', '| §3 | Prime-number input and one-sided divisor rate | open |',
'| §3 | Prime-number input, psi/log-lcm and finite-window actual-divisor rates | proved; P4 accepted, 104-module validation and 67+172 audit checks |')
replace(docs / 'PROOF_GAPS.md', '5. **§3–4, limits.** Establish a one-sided divisor rate using finite prime\n   ranges or justify the uniform periodic tail.',
'''5. **§3–4, limits. P4 arithmetic rate discharged.** Fixed finite interior
   windows give unconditional eventual actual-divisor rates. The theta/psi
   proof closure and all project bridges passed final build and axiom checks.
   The concrete rate 2/69 is only a calibration; sharp gamma remains open.''')
replace(docs / 'PROOF_GAPS.md', 'The finite product and analytic limiting steps remain open.',
'The finite product and whole-line integrable majorant are the authorized P5-A\n   target; contour deformation and central asymptotics remain subsequent work.')
replace(docs / 'LIBRARY_AUDIT.md', 'This accepts the PNT input, not the still\npending P4 application/root checks.',
'The P4 applications and complete root validation have also passed: 104\nmodules, 67 new checks and 172 regression checks; only the same three axioms.')
replace(docs / 'LIBRARY_AUDIT.md', 'Compile and run `#print axioms` on the candidate declarations and bridge the real/natural limits; candidate is not accepted yet',
'Completed in P4: audited 19-module proof subset, theta/psi scaling, natural-index log-lcm limit and actual-divisor rates; see P4 review')
replace(docs / 'TRUST.md', "Mathlib is a pinned source dependency. The candidate prime-number theorem\nproject's revision is recorded, but it is not yet a dependency. Its relevant theorem must be\ncompiled and its transitive axiom set checked before it can be used. The\ncandidate repository has unfinished unrelated declarations, so a repository-wide\nbuild or the presence of a theorem name is not evidence that its proof is free\nof `sorryAx`.",
'''Mathlib is a pinned source dependency. P4 accepts the required 19-module
proof subset of PrimeNumberTheoremAnd at the recorded revision. The unused
unfinished branch is omitted, with source provenance and license preserved.
The compiled PNT declarations and their project applications passed executed
transitive axiom checks. The full upstream package is not a dependency.''')
for name in ['TRUST.md', 'LUNA_HANDOFF.md']:
    with (docs / name).open('a', encoding='utf-8') as f:
        f.write('''

## P4 final acceptance and P5-A handoff — 29 October 2026

P4 is accepted. Complete dependency validation covers 104 current modules;
the final run executed 25 targets, reused 79 source-identical verified records,
and built the full root afresh (3963 jobs). Fresh audits cover exactly 67 new
checks and 172 regression checks, with only propext, Classical.choice and
Quot.sound. Peak final build 3556.75 MiB; peak audit 5105.83 MiB, below 6144.
See ../P4_REVIEW_2026-10-28.md and logs/p4-acceptance-2026-10-28.json.

The concrete actual divisor has rate 2/69 with arbitrary positive slack;
the general finite-window and scaled-grouping interfaces are proved. Sharp
gamma evaluation and final numerical pi-power bounds are not established.

P5-A is newly authorized: ../P5A_HORIZONTAL_GOAL.md. Work on actual finite
denominator products and whole-line integrability. Preserve P1–P4 acceptance,
toolchain, manifest, caches and the unchanged single-compiler memory guard.
Do not repeat accepted P2/PNT checks or revive the obsolete blocked thread.
''')

agents = (root / 'AGENTS.md').read_text(encoding='utf-8')
agents = agents.replace('The user has now explicitly authorized\nP4; read `formalization/P4_PRIME_RATE_GOAL.md` for its scope and acceptance.\nP5 and numerical bounds remain later stages.',
'''P4 is also accepted; see `formalization/P4_REVIEW_2026-10-28.md` and its
machine-readable evidence. The user explicitly authorized P5-A on 29 October;
read `formalization/P5A_HORIZONTAL_GOAL.md` for its scope and acceptance.
Remaining P5 work and numerical bounds stay outside this stage.''')
for path in [root / 'AGENTS.md', Path(r'C:\Users\hc260\OneDrive\文档\ChatGPT\pi无理测度记录突破\AGENTS.md')]:
    path.write_text(agents, encoding='utf-8')
print('P4 documentation reconciled; Lean sources unchanged.')
