"""Accept complete P6 only after the full root and exact axiom audits pass."""
from pathlib import Path
import hashlib,json,re,sys
from vendor_stirling_log_core import rendered_core
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
workspace=Path(__file__).resolve().parents[1]
project=workspace/'formalization/OddPiPowers'; logs=project/'logs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
state=json.loads((logs/'p6-guarded-library-build-state.json').read_text())
expected=json.loads((logs/'p6-audit-expected.json').read_text())
assert state['status']=='completed' and state['exit_code']==0
assert state['final_root_validated'] and state['completed'][-1]['module']=='OddPiPowers'
assert 'validation' not in state['completed'][-1]
assert state['plan']==expected['library_plan']==[r['module'] for r in state['completed']]
assert len(state['plan'])==len(set(state['plan']))
assert len(state['plan'])==264 and len(expected['new_modules'])==100
assert len(expected['new'])==424
baseline=json.loads((logs/'p6b-guarded-library-build-state.json').read_text())
assert len(baseline['plan'])==164
for row in baseline['completed']:
    p=logs/'p6b-accepted-root.lean.txt' if row['module']=='OddPiPowers' else project/(row['module'].replace('.','/')+'.lean')
    assert sha(p)==row['source_sha256'],('Changed accepted P6-B source',p)
for p,digest in expected['source_sha256'].items():assert sha(project/p)==digest,p
prior={}
for p in logs.glob('*guarded-library-build-state*.json'):
    if p.name=='p6-guarded-library-build-state.json':continue
    for row in json.loads(p.read_text()).get('completed',[]):
        prior[(row['module'],row['source_sha256'],row['log'])]=p.name
def checked_job(p):
    j=json.loads(p.read_text())
    assert j['process_completed'] and j['exit_code']==0,p
    assert j['job_cap_MiB']==6144 and j['peak_job_MiB']<=6144,p
    return j
jobs=[];executed=[];reuse={}
for row in state['completed']:
    assert sha(project/(row['module'].replace('.','/')+'.lean'))==row['source_sha256']
    j=checked_job((project/row['log']).with_suffix('.job.json'));jobs.append(j)
    if 'validation' in row:
        key=(row['module'],row['source_sha256'],row['log'])
        assert key in prior,row
        name=prior[key];reuse[name]=reuse.get(name,0)+1
    else:executed.append(j)
def audit(filename,names):
    p=logs/filename;s=p.read_text(encoding='utf-8')
    rows=re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]",s,re.M)
    empty=re.findall(r"^'(.+)' does not depend on any axioms",s,re.M)
    actual=[n for n,_ in rows]+empty
    assert len(actual)==len(set(actual))==len(names),filename
    assert set(actual)==set(names),filename
    axioms={a.strip() for _,v in rows for a in v.split(',') if a.strip()}
    assert axioms<={'propext','Classical.choice','Quot.sound'},(filename,axioms)
    return dict(log=filename,count=len(actual),axioms=sorted(axioms),job=checked_job(p.with_suffix('.job.json')))
audits=[audit('p6-post-build-axioms.log',expected['new']),
        audit('p6-post-build-regression-axioms.log',expected['regression'])]
signature_log=(logs/'p6-post-build-axioms.log').read_text(encoding='utf-8')
for name in ['p6TwelveLayer_actualFamily','pi_cube_exponentUpperBound_42170551935_div_35026168',
             'pi_cube_exponentUpperBound_lt_1203973_div_1000',
             'pi_cube_not_liouvilleWith_1203973_div_1000']:
    assert f'OddPiPowers.{name} :' in signature_log,('Missing compiled signature',name)
assert len(expected['regression'])==602
manifest=sha(project/'lake-manifest.json')
assert manifest=='e46b8f7bf97f5d4ee8f0b4f5155b71dbead74f1c2aef1b55c34677ffbd9dbf38'
assert (project/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
vendor=project/'OddPiPowers/Vendor/PNT'
for row in json.loads((vendor/'PROVENANCE.json').read_text())['files']:
    assert sha(vendor/row['file'])==row['adapted_sha256']
core=json.loads((logs/'p5e-stirling-core-provenance.json').read_text())
original=project/'.lake/packages/mathlib'/core['source'];adapted=project/core['adapted']
assert sha(original)==core['source_sha256'] and sha(adapted)==core['adapted_sha256']
assert adapted.read_text(encoding='utf-8')==rendered_core(original.read_text(encoding='utf-8'))
for mod in state['plan']:
    p=project/(mod.replace('.','/')+'.lean')
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',p.read_text(encoding='utf-8-sig')),p
required={'OddPiPowers.pi_cube_exponentUpperBound_42170551935_div_35026168',
    'OddPiPowers.pi_cube_exponentUpperBound_lt_1203973_div_1000',
    'OddPiPowers.p6TwelveLayer_actualFamily',
    'OddPiPowers.PrimeRates.p6_actualDivisor_eventually_exp_lower',
    'OddPiPowers.actual_reduced_auxiliaryFamily',
    'OddPiPowers.PrimeRates.periodFloorCheck_sound',
    'OddPiPowers.PrimeRates.periodBlockCheck_sound',
    'OddPiPowers.PrimeRates.tailFloorCheck_sound',
    'OddPiPowers.PrimeRates.periodTail_eq_fraction',
    'OddPiPowers.PrimeRates.rational_tail_step_identity',
    'OddPiPowers.PrimeRates.p6_prefix_floor_lower',
    'OddPiPowers.PrimeRates.p6_tail_floor_lower',
    'OddPiPowers.p6_actualDecay_lower','OddPiPowers.p6_actualGrowth_upper'}
for i in range(30):
    required.update(f'OddPiPowers.PrimeRates.p6Period{kind}{i:02d}_checked' for kind in ['Prefix','Tail'])
for i in range(12):required.add(f'OddPiPowers.p6CentralInterval{i:02d}_lower')
assert required<=set(expected['new'])
from fractions import Fraction as F
assert F(42170551935,35026168)<F(1203973,1000)
result=dict(status='accepted',date='2026-10-30',stage='Complete P6 twelve-layer pi-cube bound',
    bound='42170551935/35026168',strict_target='1203973/1000',
    fixed_parameters=dict(s=11,M=187,m=186,L=69,Y='2113/20',gamma='4543599/100000',
        D='651297284/1000000',G='255596306/1000000'),
    library_modules=len(state['plan']),new_modules=len(expected['new_modules']),
    executed_build_targets=state['executed_count'],verified_cached_modules=state['reused_count'],
    build_run=state['run'],verified_cache_evidence=reuse,
    peak_build_job_MiB=max(j['peak_job_MiB'] for j in executed),
    peak_all_build_evidence_MiB=max(j['peak_job_MiB'] for j in jobs),audits=audits,
    manifest_sha256=manifest,unchanged_prior_mathematical_modules=163,
    resource_contract=dict(job_cap_MiB=6144,lean_cap_MiB=2048,workers=1,max_trial_seconds=300,
      runner_sha256=sha(workspace/'scripts/bounded_lean.py'),
      serial_driver_sha256=sha(workspace/'scripts/guarded_library_build.py'),
      library_configuration_sha256=sha(project/'lakefile.toml')),
    data_provenance=dict(accepted_cell_data_sha256=sha(project/'OddPiPowers/Arithmetic/TwelveLayerCellChunks.lean'),
      prefix_tail_generator_sha256=sha(workspace/'scripts/generate_p6_period_prefix.py'),
      central_generator_sha256=sha(workspace/'scripts/generate_p6_central_certificates.py')),
    stirling_core_provenance=core,source_sha256=expected['source_sha256'],
    scope='Actual scaled twelve-layer integral quotient, general uniform heights and central rates, '
      'finite certified divisor windows with rational telescoping tail, exact numerical log/atan/pi '
      'certificates and an unconditional pi-cube exponent strictly below1203.973. '
      'No auxiliary-family, analytic, prime-rate, or numerical hypotheses remain in the fixed theorem.')
(logs/'p6-acceptance-2026-10-30.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ('source_sha256','stirling_core_provenance')},indent=2))
