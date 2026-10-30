"""Prepare/import-check L99's final signatures, or verify executed acceptance.

No compiler is launched here. The audit itself must be compiled through the
unchanged bounded_lean.py after all new modules have compiled successfully.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'formalization/OddPiPowers'
LOGS=PROJECT/'logs'
AUDIT=PROJECT/'L99AcceptanceAudit.lean'
DECLARATIONS=[
 'OddPiPowers.L99.twentyEightLayerCellTable_all_valid',
 'OddPiPowers.L99.twentyEightLayerCellTable_pairwise_disjoint',
 'OddPiPowers.L99.twentyEightLayerLowerBound_le_cost',
 'OddPiPowers.L99.scaledTwentyEightLayerActualGrouping',
 'OddPiPowers.L99.scaledTwentyEightLayer_shapeRelativeLength',
 'OddPiPowers.L99.l99_actualDecay_lower',
 'OddPiPowers.L99.l99_actualGrowth_upper',
 'OddPiPowers.L99.PrimeRates.l99_prefix_floor_lower',
 'OddPiPowers.L99.PrimeRates.l99_tail_floor_lower',
 'OddPiPowers.L99.PrimeRates.l99_finite_window_rate_lower',
 'OddPiPowers.L99.PrimeRates.l99_actualDivisor_eventually_exp_lower',
 'OddPiPowers.L99.l99_actualFamily',
 'OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact',
 'OddPiPowers.L99.pi_cube_exponentUpperBound_lt_110793_div_100',
 'OddPiPowers.L99.pi_cube_not_liouvilleWith_110793_div_100',
]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def prepare():
    text='module\npublic import OddPiPowers.L99.Transfer.PiCube\n\n'
    text+='example : OddPiPowers.ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979) :=\n'
    text+='  OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact\n\n'
    text+='example : ∃ B : ℝ, B < 110793 / 100 ∧ OddPiPowers.ExponentUpperBound (Real.pi ^ 3) B :=\n'
    text+='  OddPiPowers.L99.pi_cube_exponentUpperBound_lt_110793_div_100\n\n'
    text+='example : ¬ LiouvilleWith (110793 / 100) (Real.pi ^ 3) :=\n'
    text+='  OddPiPowers.L99.pi_cube_not_liouvilleWith_110793_div_100\n\n'
    text+='example : OddPiPowers.AuxiliaryFamily 171 99 (54469491 / 100000) (2672657 / 12500)\n'
    text+='    OddPiPowers.L99.l99Rows := OddPiPowers.L99.l99_actualFamily\n\n'
    text+='\n'.join('#print axioms '+name for name in DECLARATIONS)+'\n'
    AUDIT.write_text(text,encoding='utf-8')
    print('Prepared',AUDIT.relative_to(ROOT),'; NOT yet compiled.')

def verify():
    state=json.loads((LOGS/'l99-build-state.json').read_text(encoding='utf-8'))
    assert state['status']=='completed' and state['target']=='OddPiPowers.L99.Transfer.PiCube'
    records={row['module']:row for row in state['completed']}
    sources={};peaks=[]
    for name in state['plan']:
        row=records[name];path=PROJECT/(name.replace('.','/')+'.lean')
        assert sha(path)==row['source_sha256'],name
        source=path.read_text(encoding='utf-8')
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source),name
        assert (PROJECT/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')).is_file(),name
        logfile=PROJECT/row['log'];job=json.loads(logfile.with_suffix('.job.json').read_text())
        assert job['process_completed'] and job['exit_code']==0 and job['job_cap_MiB']==6144,name
        assert job['peak_job_MiB']<=6144,name
        assert not re.search(r'\berror:|declaration uses .sorry.',logfile.read_text(encoding='utf-8',errors='replace')),name
        sources[str(path.relative_to(PROJECT))]=sha(path);peaks.append(job['peak_job_MiB'])
    # Preserve all prior accepted mathematical modules, including the old root.
    prior=json.loads((LOGS/'p6-guarded-library-build-state.json').read_text(encoding='utf-8'))
    for row in prior['completed']:
        p=PROJECT/(row['module'].replace('.','/')+'.lean')
        assert sha(p)==row['source_sha256'],row['module']
    p6=json.loads((LOGS/'p6-acceptance-2026-10-30.json').read_text(encoding='utf-8'))
    assert sha(PROJECT/'lake-manifest.json')==p6['manifest_sha256']
    assert (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
    pinned_dependencies={}
    for dep in json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf-8'))['packages']:
        revision=subprocess.check_output(['git','rev-parse','HEAD'],
            cwd=PROJECT/'.lake/packages'/dep['name'],text=True).strip()
        assert revision==dep['rev'],dep['name']
        pinned_dependencies[dep['name']]=revision
    audit_log=LOGS/'l99-acceptance-axioms.log'
    job=json.loads(audit_log.with_suffix('.job.json').read_text())
    assert job['process_completed'] and job['exit_code']==0 and job['job_cap_MiB']==6144
    text=audit_log.read_text(encoding='utf-8')
    found={name:set(filter(None,(v.strip() for v in axioms.split(','))))
           for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
    assert set(found)==set(DECLARATIONS),(set(found),set(DECLARATIONS))
    allowed={'propext','Classical.choice','Quot.sound'}
    assert all(values<=allowed for values in found.values()),found
    assert not re.search(r'\berror:|sorryAx|native_decide|Lean\.ofReduceBool',text)
    report=dict(status='accepted',date='2026-10-31',stage='L99 parameter optimization using the existing transfer',
      bound='12970477737/11706979',strict_target='110793/100',
      fixed_parameters=dict(L=99,offsets=list(range(28)),counts=[64]+[4]*27,M=172,m=171,Y='1801/20',
                            gamma='2761813/50000',D='54469491/100000',G='2672657/12500'),
      new_closure_modules=len(state['plan']),compiled_modes=sorted({records[n]['mode'] for n in state['plan']}),
      compilation='Each new dependency module compiled separately through bounded_lean.py; final entry and signature/axiom audit executed.',
      peak_build_job_MiB=max(peaks),audit=dict(log=str(audit_log.relative_to(PROJECT)),declarations=DECLARATIONS,
        axioms=sorted(set().union(*found.values())),job=job),
      unchanged_prior_mathematical_modules=len(prior['completed']),manifest_sha256=sha(PROJECT/'lake-manifest.json'),
      pinned_dependencies=pinned_dependencies,
      source_sha256=sources,generator_sha256=sha(ROOT/'scripts/generate_l99_instance.py'),
      runner_sha256=sha(ROOT/'scripts/bounded_lean.py'),audit_source_sha256=sha(AUDIT),
      scope='Fixed unconditional pi-cube application only; cofactor improvements and higher-power numerical applications not accepted.')
    (LOGS/'l99-acceptance-2026-10-31.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k not in {'source_sha256','audit'}},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--prepare',action='store_true');a=p.parse_args()
    prepare() if a.prepare else verify()
