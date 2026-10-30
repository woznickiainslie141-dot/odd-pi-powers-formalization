"""Verify completed P4 build, exact axiom audit sets and source provenance."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

workspace=Path(__file__).resolve().parent.parent
project=workspace/'formalization/OddPiPowers'
logs=project/'logs'
allowed={'propext','Classical.choice','Quot.sound'}
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
state=json.loads((logs/'p4-guarded-library-build-state.json').read_text(encoding='utf-8'))
assert state['status']=='completed' and state['exit_code']==0
assert state['final_root_validated'] and state['completed'][-1]['module']=='OddPiPowers'
assert 'validation' not in state['completed'][-1]
assert [r['module'] for r in state['completed']]==state['plan']
assert state['completed'][-1]['log'].endswith(state['run']+'.log')
prior_ledgers=[logs/'p3b-guarded-library-build-state.json',
    *logs.glob('p4-guarded-library-build-state-*.json')]
prior_records={}
for ledger in prior_ledgers:
    previous=json.loads(ledger.read_text(encoding='utf-8'))
    for row in previous.get('completed',[]):
        prior_records[(row['module'],row['source_sha256'],row['log'])]=ledger.name
reuse_evidence={}
records=[]
for row in state['completed']:
    src=project/(row['module'].replace('.','/')+'.lean')
    assert sha(src)==row['source_sha256'],f'Stale source: {src}'
    job=json.loads((project/row['log']).with_suffix('.job.json').read_text())
    assert job['process_completed'] and job['exit_code']==0,row['log']
    assert job['job_cap_MiB']==6144 and job['peak_job_MiB']<=6144
    if 'validation' in row:
        key=(row['module'],row['source_sha256'],row['log'])
        assert key in prior_records,f'No prior record for reused module: {row["module"]}'
        reference=prior_records[key]
        reuse_evidence[reference]=reuse_evidence.get(reference,0)+1
    records.append(job)

def audit(logfile,expected):
    log=logs/logfile
    text=log.read_text(encoding='utf-8')
    found=re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]",text,re.M)
    # Some purely constructive definitions have an empty axiom set.
    empty=re.findall(r"^'(.+)' does not depend on any axioms",text,re.M)
    names=[n for n,_ in found]+empty
    assert set(names)==set(expected) and len(names)==len(set(names)),logfile
    axioms=set()
    for _, values in found:
        axioms.update(v.strip() for v in values.split(',') if v.strip())
    assert axioms<=allowed,(logfile,axioms)
    job=json.loads(log.with_suffix('.job.json').read_text())
    assert job['process_completed'] and job['exit_code']==0
    assert job['peak_job_MiB']<=6144
    return dict(log=logfile,count=len(names),axioms=sorted(axioms),job=job)

p4_expected=json.loads((logs/'p4-audit-expected.json').read_text())
p3_expected=re.findall(r'^#print axioms (\S+)',(project/'AxiomAudit.lean').read_text(encoding='utf-8'),re.M)
audits=[audit('p4-post-build-axioms.log',p4_expected),
        audit('p4-post-build-regression-axioms.log',p3_expected)]
manifest=sha(project/'lake-manifest.json')
assert manifest.upper()=='E46B8F7BF97F5D4EE8F0B4F5155B71DBEAD74F1C2AEF1B55C34677FFBD9DBF38'
vendor=project/'OddPiPowers/Vendor/PNT'
provenance=json.loads((vendor/'PROVENANCE.json').read_text())
assert provenance['revision']=='127b50e33f6033e2147921167a117af96d9ba4ea'
for row in provenance['files']:
    assert sha(vendor/row['file'])==row['adapted_sha256'],row['file']
for source in (project/'OddPiPowers').rglob('*.lean'):
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source.read_text(encoding='utf-8')),source
result=dict(status='accepted',date='2026-10-28',stage='P4 finite-window divisor rates',
    library_modules=len(state['plan']),build_run=state['run'],
    executed_build_targets=state['executed_count'],verified_cached_modules=state['reused_count'],
    verified_cache_evidence=reuse_evidence,
    peak_build_job_MiB=max(r['peak_job_MiB'] for r in records),audits=audits,
    manifest_sha256=manifest,vendor_revision=provenance['revision'],
    vendor_modules=len(provenance['files']),
    scope='Unconditional PNT/psi/lcm interfaces, general finite windows/periods and scaled '
      'actual-divisor exponent rates, with concrete rate 2/69. Sharp gamma arithmetic, '
      'P5 analytic estimates and final numerical pi-power bounds remain open.')
(logs/'p4-acceptance-2026-10-28.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
