"""Verify P5-B source freeze, prior acceptance preservation and exact audits."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
workspace = Path(__file__).resolve().parent.parent
project = workspace / 'formalization/OddPiPowers'
logs = project / 'logs'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
state = json.loads((logs / 'p5b-guarded-library-build-state.json').read_text(encoding='utf-8'))
assert state['status'] == 'completed' and state['exit_code'] == 0
assert state['final_root_validated'] and state['completed'][-1]['module'] == 'OddPiPowers'
assert 'validation' not in state['completed'][-1]
assert [row['module'] for row in state['completed']] == state['plan']
assert len(state['plan']) == len(set(state['plan'])) == 122

prior_paths = [logs / f'{stage}-guarded-library-build-state.json' for stage in ['p3b', 'p4', 'p5a']]
prior_paths += list(logs.glob('p5b-guarded-library-build-state-*.json'))
prior = {}
for path in prior_paths:
    ledger = json.loads(path.read_text(encoding='utf-8'))
    for row in ledger.get('completed', []):
        prior[(row['module'], row['source_sha256'], row['log'])] = path.name

jobs, executed_jobs, reuse = [], [], {}
for row in state['completed']:
    source = project / (row['module'].replace('.', '/') + '.lean')
    assert sha(source) == row['source_sha256'], source
    job = json.loads((project / row['log']).with_suffix('.job.json').read_text())
    assert job['process_completed'] and job['exit_code'] == 0, row
    assert job['job_cap_MiB'] == 6144 and job['peak_job_MiB'] <= 6144, row
    if 'validation' in row:
        key = (row['module'], row['source_sha256'], row['log'])
        assert key in prior, row
        reuse[prior[key]] = reuse.get(prior[key], 0) + 1
    else:
        executed_jobs.append(job)
    jobs.append(job)

previous = json.loads((logs / 'p5a-guarded-library-build-state.json').read_text(encoding='utf-8'))
for row in previous['completed']:
    source = project / (row['module'].replace('.', '/') + '.lean')
    if row['module'] == 'OddPiPowers':
        source = logs / 'p5a-accepted-root.lean.txt'
    assert sha(source) == row['source_sha256'], ('Changed accepted source', source)

expected = json.loads((logs / 'p5b-audit-expected.json').read_text(encoding='utf-8'))
assert len(expected['source_sha256']) == 11
for path, digest in expected['source_sha256'].items():
    assert sha(project / path) == digest, path

def audit(filename, names):
    path = logs / filename
    text = path.read_text(encoding='utf-8')
    rows = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", text, re.M)
    empty = re.findall(r"^'(.+)' does not depend on any axioms", text, re.M)
    actual = [name for name, _ in rows] + empty
    assert len(actual) == len(set(actual)) == len(names), filename
    assert set(actual) == set(names), filename
    axioms = {a.strip() for _, values in rows for a in values.split(',') if a.strip()}
    assert axioms <= allowed, (filename, axioms)
    job = json.loads(path.with_suffix('.job.json').read_text())
    assert job['process_completed'] and job['exit_code'] == 0, filename
    assert job['job_cap_MiB'] == 6144 and job['peak_job_MiB'] <= 6144
    return dict(log=filename, count=len(actual), axioms=sorted(axioms), job=job)

audits = [audit('p5b-post-build-axioms.log', expected['new']),
          audit('p5b-post-build-regression-axioms.log', expected['regression'])]
assert len(expected['regression']) == 294
manifest = sha(project / 'lake-manifest.json')
assert manifest == 'e46b8f7bf97f5d4ee8f0b4f5155b71dbead74f1c2aef1b55c34677ffbd9dbf38'
assert (project / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
vendor = project / 'OddPiPowers/Vendor/PNT'
provenance = json.loads((vendor / 'PROVENANCE.json').read_text())
for row in provenance['files']:
    assert sha(vendor / row['file']) == row['adapted_sha256'], row['file']
for path in (project / 'OddPiPowers').rglob('*.lean'):
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', path.read_text(encoding='utf-8')), path

result = dict(status='accepted', date='2026-10-29',
    stage='P5-B actual finite pole contours and weighted side estimates',
    library_modules=len(state['plan']), executed_build_targets=state['executed_count'],
    verified_cached_modules=state['reused_count'], build_run=state['run'], verified_cache_evidence=reuse,
    peak_build_job_MiB=max(j['peak_job_MiB'] for j in executed_jobs),
    peak_all_build_evidence_MiB=max(j['peak_job_MiB'] for j in jobs), audits=audits,
    manifest_sha256=manifest, unchanged_prior_mathematical_modules=110,
    scope='Actual remainder equals a normalized finite sum of pole-circle integrals, with exp(lambda)=I; '
          'full-factorial exponential horizontal kernels are integrable and both fixed-scale vertical sides vanish. '
          'The actual seventeen-row family is instantiated. Rectangle/circle deformation, height and central rates, '
          'sharp gamma and final numerical pi-power bounds remain open.')
(logs / 'p5b-acceptance-2026-10-29.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps(result, indent=2))
