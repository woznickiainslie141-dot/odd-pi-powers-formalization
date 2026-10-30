"""Serialize only the assigned L99 closure through the unchanged Lean guard."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys, time

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'formalization/OddPiPowers'
PREFIX='OddPiPowers.L99.'
STATE=PROJECT/'logs/l99-build-state.json'

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def source(name):return PROJECT/(name.replace('.','/')+'.lean')
def dependencies(name):
    text=source(name).read_text(encoding='utf-8')
    return [dep for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M)
            for dep in line.split() if dep=='OddPiPowers' or dep.startswith('OddPiPowers.')]

def main():
    p=argparse.ArgumentParser();p.add_argument('--target',default=PREFIX+'Transfer.PiCube')
    p.add_argument('--limit',type=int);p.add_argument('--emit',action='store_true')
    a=p.parse_args();assert a.target.startswith(PREFIX)
    plan=[];seen=set();active=set()
    def visit(name):
        if not name.startswith(PREFIX) or name in seen:return
        if name in active:raise RuntimeError('Import cycle: '+name)
        active.add(name)
        for dep in dependencies(name):visit(dep)
        active.remove(name);seen.add(name);plan.append(name)
    visit(a.target)
    # Cache identity includes every transitive project source, manifest,
    # toolchain, build flags and guard. A changed child invalidates a parent.
    fingerprint_cache={}
    fixed=[PROJECT/'lake-manifest.json',PROJECT/'lean-toolchain',PROJECT/'lakefile.toml',ROOT/'scripts/bounded_lean.py']
    def fingerprint(name):
        if name not in fingerprint_cache:
            blob=json.dumps([digest(source(name)),[fingerprint(d) for d in dependencies(name)],
                             [digest(f) for f in fixed]],sort_keys=True).encode()
            fingerprint_cache[name]=hashlib.sha256(blob).hexdigest()
        return fingerprint_cache[name]
    previous=json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {}
    records={r['module']:r for r in previous.get('completed',[])}
    state=dict(status='running',target=a.target,mode='emit' if a.emit else 'lake',
               plan=plan,completed=list(records.values()),current=None)
    def save():STATE.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
    save();executed=0
    for index,name in enumerate(plan,1):
        state['current']=name;save()
        old=records.get(name)
        artifact=PROJECT/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
        if old and old.get('fingerprint')==fingerprint(name) and artifact.is_file():
            metrics=(PROJECT/old['log']).with_suffix('.job.json')
            job=json.loads(metrics.read_text()) if metrics.exists() else {}
            if job.get('exit_code')==0 and job.get('process_completed') and job.get('job_cap_MiB')==6144 and (a.emit or old.get('mode')=='lake'):
                print(f'[{index}/{len(plan)}] verified cache {name}',flush=True);continue
        if a.limit is not None and executed>=a.limit:
            state.update(status='bounded_batch_done',current=name);save();return
        stamp=time.strftime('%Y%m%dT%H%M%S')
        logfile='logs/l99-'+name.replace('.','-')+'-'+stamp+'.log'
        args=[sys.executable,str(ROOT/'scripts/bounded_lean.py')]
        args+= [str(source(name).relative_to(PROJECT)),'--emit'] if a.emit else ['--build-target',name]
        args+=['--timeout','300','--log',logfile]
        print(f'[{index}/{len(plan)}] compiling {name}',flush=True)
        begin=time.monotonic();run=subprocess.run(args,cwd=ROOT)
        if run.returncode:
            state.update(status='failed',exit_code=run.returncode,failed_log=logfile);save()
            logpath=PROJECT/logfile
            if logpath.exists():print(logpath.read_text(encoding='utf-8',errors='replace')[-7000:],flush=True)
            raise SystemExit(run.returncode)
        record=dict(module=name,source_sha256=digest(source(name)),fingerprint=fingerprint(name),
                    log=logfile,mode='emit' if a.emit else 'lake',seconds=round(time.monotonic()-begin,3))
        records[name]=record;state['completed']=list(records.values());executed+=1;save()
    state.update(status='completed',current=None,exit_code=0);save()
    print(f'Guarded target complete: {a.target}; {executed} newly executed modules.',flush=True)

if __name__=='__main__':main()
