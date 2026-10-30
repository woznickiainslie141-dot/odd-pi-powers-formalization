"""Validate the root's project dependency closure in strict topological order."""
from pathlib import Path
from datetime import datetime
import hashlib
import json
import re
import subprocess
import sys
import argparse
import time
from bounded_lean import available

arguments=argparse.ArgumentParser()
arguments.add_argument('--prefix', choices=['p3b','p4','p5a','p5b','p5c','p5d','p5e','p6b','p6'], default='p3b')
arguments.add_argument('--reuse-verified', action='store_true',
    help='Reuse successful source-identical P4/P5 records; always build the complete root.')
options=arguments.parse_args()
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

workspace=Path(__file__).resolve().parents[1]
project=workspace/'formalization/OddPiPowers'
runner=workspace/'scripts/bounded_lean.py'
plan=[]
visiting=set()
visited=set()

def source(name):return project/(name.replace('.', '/')+'.lean')

def visit(name):
    if name in visited:return
    if name in visiting:raise RuntimeError('Import cycle: '+name)
    visiting.add(name)
    text=source(name).read_text(encoding='utf-8')
    for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M):
        for dep in line.split():
            if dep=='OddPiPowers' or dep.startswith('OddPiPowers.'):
                visit(dep)
    visiting.remove(name);visited.add(name);plan.append(name)

visit('OddPiPowers')
stamp=datetime.now().strftime('%Y%m%dT%H%M%S')
state_path=project/f'logs/{options.prefix}-guarded-library-build-state.json'
verified={}
if options.reuse_verified:
    if options.prefix not in ('p4', 'p5a', 'p5b', 'p5c', 'p5d', 'p5e', 'p6b', 'p6'):
        raise SystemExit('Verified reuse is only available for P4/P5 validation.')
    ledgers=[project/'logs/p3b-guarded-library-build-state.json']
    if options.prefix in ('p5a', 'p5b', 'p5c', 'p5d', 'p5e', 'p6b', 'p6'):
        ledgers.append(project/'logs/p4-guarded-library-build-state.json')
    if options.prefix in ('p5b', 'p5c', 'p5d', 'p5e', 'p6b', 'p6'):
        ledgers.append(project/'logs/p5a-guarded-library-build-state.json')
    if options.prefix in ('p5c', 'p5d', 'p5e', 'p6b', 'p6'):
        ledgers.append(project/'logs/p5b-guarded-library-build-state.json')
    if options.prefix in ('p5d', 'p5e', 'p6b', 'p6'):
        ledgers.append(project/'logs/p5c-guarded-library-build-state.json')
    if options.prefix in ('p5e', 'p6b', 'p6'):
        ledgers.append(project/'logs/p5d-guarded-library-build-state.json')
    if options.prefix in ('p6b', 'p6'):
        ledgers.append(project/'logs/p5e-guarded-library-build-state.json')
    if options.prefix=='p6':
        ledgers.append(project/'logs/p6b-guarded-library-build-state.json')
    for ledger in [*ledgers,state_path]:
        if not ledger.exists():continue
        previous=json.loads(ledger.read_text(encoding='utf-8'))
        for row in previous.get('completed',[]):
            name=row['module']
            if name=='OddPiPowers' or not source(name).exists():continue
            if hashlib.sha256(source(name).read_bytes()).hexdigest()!=row['source_sha256']:continue
            artifact=project/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
            metrics=(project/row['log']).with_suffix('.job.json')
            if not artifact.is_file() or not metrics.is_file():continue
            job=json.loads(metrics.read_text())
            if not job['process_completed'] or job['exit_code']!=0 or job['job_cap_MiB']!=6144:continue
            verified[name]={**row,'validation':'source-identical verified cache; final root revalidates graph',
                            'evidence_ledger':str(ledger.relative_to(project))}
    if state_path.exists():
        previous=json.loads(state_path.read_text(encoding='utf-8'))
        snapshot=project/f"logs/{options.prefix}-guarded-library-build-state-{previous['run']}.json"
        if not snapshot.exists():snapshot.write_bytes(state_path.read_bytes())
state={'run':stamp,'plan':plan,'completed':[],'status':'running','current':None,
       'reused_count':0,'executed_count':0,'final_root_validated':False}
def save():state_path.write_text(json.dumps(state,indent=2),encoding='utf-8')
save()
for i,name in enumerate(plan,1):
    state['current']=name;save()
    if name in verified:
        state['completed'].append(verified[name])
        state['reused_count']+=1;save()
        print(f'[{i}/{len(plan)}] verified cache {name}',flush=True)
        continue
    if options.prefix in ('p4', 'p5a', 'p5b', 'p5c', 'p5d', 'p5e', 'p6b', 'p6'):
        time.sleep(2)
        wait_begin=time.monotonic()
        while True:
            memory=available()
            if memory.free_phys >= 2560*2**20 and memory.free_commit >= 12288*2**20:
                break
            if time.monotonic()-wait_begin>45:
                state.update(status='resource_wait',exit_code=75);save()
                raise SystemExit('Launch threshold not recovered; no compiler started.')
            time.sleep(1)
    print(f'[{i}/{len(plan)}] {name}',flush=True)
    logfile='logs/'+options.prefix+'-lake-'+name.replace('.','-')+'-'+stamp+'.log'
    result=subprocess.run([sys.executable,str(runner),'--build-target',name,
                           '--timeout','300','--log',logfile],cwd=workspace)
    if result.returncode:
        state.update(status='failed',exit_code=result.returncode,failed_log=logfile);save()
        data=(project/logfile).read_text(encoding='utf-8',errors='replace') if (project/logfile).exists() else ''
        print('\n'.join(line[:600] for line in data.splitlines()[-12:]),flush=True)
        raise SystemExit(result.returncode)
    state['completed'].append({'module':name,'source_sha256':hashlib.sha256(source(name).read_bytes()).hexdigest(),'log':logfile})
    state['executed_count']+=1
    if name=='OddPiPowers':state['final_root_validated']=True
    save()
state.update(status='completed',current=None,exit_code=0);save()
print(f"Complete guarded Lake library validation passed: {len(plan)} dependency modules, "
      f"{state['executed_count']} executed targets, {state['reused_count']} verified cached records, complete root built.",flush=True)
