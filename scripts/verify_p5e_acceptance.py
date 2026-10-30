"""Verify actual central-rate and P6 certificate-soundness acceptance."""
from pathlib import Path
import hashlib
import json
import re
import sys
from vendor_stirling_log_core import rendered_core

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
workspace=Path(__file__).resolve().parents[1]
project=workspace/'formalization/OddPiPowers'
logs=project/'logs'
sha=lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
state=json.loads((logs/'p5e-guarded-library-build-state.json').read_text())
assert state['status']=='completed' and state['exit_code']==0
assert state['final_root_validated'] and state['completed'][-1]['module']=='OddPiPowers'
assert 'validation' not in state['completed'][-1]
assert [row['module'] for row in state['completed']]==state['plan']
assert len(state['plan'])==len(set(state['plan']))==151
prior_paths=[logs/f'{stage}-guarded-library-build-state.json'
    for stage in ['p3b','p4','p5a','p5b','p5c','p5d']]
prior_paths+=list(logs.glob('p5e-guarded-library-build-state-*.json'))
prior={}
for path in prior_paths:
    for row in json.loads(path.read_text()).get('completed',[]):
        prior[(row['module'],row['source_sha256'],row['log'])]=path.name

def checked_job(path):
    job=json.loads(path.read_text())
    assert job['process_completed'] and job['exit_code']==0,path
    assert job['job_cap_MiB']==6144 and job['peak_job_MiB']<=6144,path
    return job

jobs,executed,reuse=[],[],{}
for row in state['completed']:
    assert sha(project/(row['module'].replace('.','/')+'.lean'))==row['source_sha256']
    job=checked_job((project/row['log']).with_suffix('.job.json'))
    if 'validation' in row:
        key=(row['module'],row['source_sha256'],row['log'])
        assert key in prior,row
        reuse[prior[key]]=reuse.get(prior[key],0)+1
    else:
        executed.append(job)
    jobs.append(job)
previous=json.loads((logs/'p5d-guarded-library-build-state.json').read_text())
for row in previous['completed']:
    source=project/(row['module'].replace('.','/')+'.lean')
    if row['module']=='OddPiPowers':source=logs/'p5d-accepted-root.lean.txt'
    assert sha(source)==row['source_sha256'],('Changed accepted source',source)
expected=json.loads((logs/'p5e-audit-expected.json').read_text())
assert len(expected['source_sha256'])==11 and len(expected['new'])==50
assert len(expected['regression'])==471
for path,digest in expected['source_sha256'].items():assert sha(project/path)==digest,path

def audit(filename,names):
    path=logs/filename
    content=path.read_text(encoding='utf-8')
    rows=re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]",content,re.M)
    empty=re.findall(r"^'(.+)' does not depend on any axioms",content,re.M)
    actual=[name for name,_ in rows]+empty
    assert len(actual)==len(set(actual))==len(names),filename
    assert set(actual)==set(names),filename
    axioms={a.strip() for _,values in rows for a in values.split(',') if a.strip()}
    assert axioms<={'propext','Classical.choice','Quot.sound'},(filename,axioms)
    return dict(log=filename,count=len(actual),axioms=sorted(axioms),job=checked_job(path.with_suffix('.job.json')))

audits=[audit('p5e-post-build-axioms.log',expected['new']),
        audit('p5e-post-build-regression-axioms.log',expected['regression'])]
manifest=sha(project/'lake-manifest.json')
assert manifest=='e46b8f7bf97f5d4ee8f0b4f5155b71dbead74f1c2aef1b55c34677ffbd9dbf38'
assert (project/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
vendor=project/'OddPiPowers/Vendor/PNT'
for row in json.loads((vendor/'PROVENANCE.json').read_text())['files']:
    assert sha(vendor/row['file'])==row['adapted_sha256']
core=json.loads((logs/'p5e-stirling-core-provenance.json').read_text())
original=project/'.lake/packages/mathlib'/core['source']
adapted=project/core['adapted']
assert sha(original)==core['source_sha256'] and sha(adapted)==core['adapted_sha256']
assert adapted.read_text(encoding='utf-8')==rendered_core(original.read_text(encoding='utf-8'))
for path in (project/'OddPiPowers').rglob('*.lean'):
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',path.read_text(encoding='utf-8')),path
result=dict(status='accepted',date='2026-10-29',
    stage='P5-E actual central rates and P6-A rational certificate soundness',
    library_modules=len(state['plan']),executed_build_targets=state['executed_count'],
    verified_cached_modules=state['reused_count'],build_run=state['run'],verified_cache_evidence=reuse,
    peak_build_job_MiB=max(j['peak_job_MiB'] for j in executed),
    peak_all_build_evidence_MiB=max(j['peak_job_MiB'] for j in jobs),audits=audits,
    manifest_sha256=manifest,unchanged_prior_mathematical_modules=139,stirling_core_provenance=core,
    scope='Actual-grid Riemann limits with endpoints, factorial log rate, actual center and common-scale rates, '
          'uniform actual/reduced remainder exponent bounds for all seventeen rows; P6 one-sided rational '
          'rate-certificate monotonicity and soundness connected to the existing conditional transfer. '
          'Coefficient heights, complete actual AuxFamily, sharp gamma, concrete numerical bounds and '
          'general odd-power parameter closure remain open; P6 numerical closure is not claimed.')
(logs/'p5e-acceptance-2026-10-29.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
