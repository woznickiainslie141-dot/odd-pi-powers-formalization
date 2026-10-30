"""Recheck archived improvement candidates; never changes accepted Lean sources.

Each Arb replay is one isolated, 1536 MiB Windows job, at most 240 seconds.
No Lean/compiler is launched. Results are numerical certificates, not a Lean
acceptance. The proposed cofactor exponent is explicitly marked unformalized.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys,time,hashlib,re

ROOT=Path(__file__).resolve().parents[1]
PLAN=ROOT/'output/pdf/odd_pi_powers_notes/improvement_plan'
OUT=PLAN/'experiments/p6_review_2026-10-30'
CASES={
 'L69':(69,list(range(20)),[66]+[6]*16+[4]*3,'1133.65',F(9173,100)),
 'L99':(99,list(range(28)),[64]+[4]*27,'1107.93',F(1801,20)),
 'L129':(129,list(range(37)),[63]+[3]*36,'1093.59',None),
 'L175':(175,list(range(40)),[54]+[3]*39,'1082.63',None),
}

def audit_archives():
    """Cheap exact consistency checks; this does NOT replay the arc computation."""
    def interval(s):
        match=re.fullmatch(r'\[([^ ]+) \+/- ([^ ]+)\]',s)
        if not match:raise ValueError(s)
        center,radius=map(F,match.groups())
        assert radius>=0
        return center-radius,center+radius
    results=[]
    for name,relative in [
      ('L99','experiments/cert_k3_L99_T27_a64_b4.json'),
      ('L69','experiments/N1_k3_search/cert_k3_L69_m173_n20.json')]:
        path=PLAN/relative; row=json.loads(path.read_text(encoding='utf-8'))
        m=row['m']; assert sum(row['counts'])-1==m
        assert len(row['counts'])==len(row['offsets'])
        assert row['offsets']==sorted(set(row['offsets']))
        assert row['offsets'][0]==0 and 2*row['offsets'][-1]<row['L']
        assert min(row['counts'])>0
        D,G,E=map(interval,[row['D'],row['G'],row['E']])
        gap=(D[0]-2*G[1],D[1]-2*G[0])
        assert G[0]>0 and gap[0]>0
        recomputed=(m*(D[0]+G[0])/gap[1],m*(D[1]+G[1])/gap[0])
        assert max(E[0],recomputed[0])<=min(E[1],recomputed[1])
        assert E[1]<F(row['strict_upper'])
        scale=F(m-2,m); adjusted=(E[0]*scale,E[1]*scale)
        results.append(dict(case=name,source=relative,
          source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
          m=m,critical_cell_count=row['critical_cell_count'],
          archived_original_exponent=row['E'],strict_original_upper=row['strict_upper'],
          proposed_cofactor_exponent_decimal=float(sum(adjusted)/2),
          proposed_cofactor_upper='1094.97' if name=='L99' else '1120.54',
          proposed_cofactor_comparison=adjusted[1]<F('1094.97' if name=='L99' else '1120.54')))
        assert results[-1]['proposed_cofactor_comparison']
    output=dict(status='exact checks of ARCHIVED interval records only; no fresh arc/Arb replay',
      checks='parameter admissibility, positive gap, consistency of E with D/G, rational rescaling',
      caveat='Does not independently re-establish gamma, central rates or a Lean theorem.',cases=results)
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'archived_interval_audit.json').write_text(json.dumps(output,indent=2),encoding='utf-8')
    print(json.dumps(output,indent=2))

def child(name):
    sys.path.insert(0,str(ROOT/'output/pdf/odd_pi_powers_notes/code'))
    from certify import certify,ball,arb
    L,offsets,counts,upper,Yfix=CASES[name]
    t0=time.monotonic()
    print('Replay',name,'m=',sum(counts)-1,flush=True)
    row,values=certify(3,L,offsets,counts,upper)
    # Parameter selection by a decimal approximation is only a search step;
    # the following fixed rational height is rechecked entirely with Arb.
    if Yfix is None:Yfix=F(f'{float(values[0].mid()):.3f}')
    Y=ball(Yfix); gamma=values[3]; m=row['m']
    cs=[F(L-2*t,L) for t in offsets]
    D0=sum((nu*(ball(c)/2*(Y**2+ball(c)**2/4).log()-
          ball(c)*ball(c).log()+2*Y*(ball(c)/(2*Y)).atan())
          for c,nu in zip(cs,counts)),arb(0))-arb.pi()/2*Y-m
    G0=m+sum((nu*ball(c) for c,nu in zip(cs,counts)),arb(0))*arb(2).log()
    D,G=D0+gamma,G0-gamma; gap=D-2*G
    E=m*(D+G)/gap
    assert G>0 and gap>0 and E<arb(upper)
    adjusted=E*ball(F(m-2,m))
    row.pop('nonzero_merged_cells')
    result=dict(status='fresh Arb replay; NOT Lean-formalized',case=name,
      original_saddle_certificate=row,fixed_rational_height=str(Yfix),
      fixed_rates=dict(D0=str(D0),G0=str(G0),gamma=str(gamma),D=str(D),G=str(G),gap=str(gap)),
      fixed_original_exponent=str(E),strict_original_upper=upper,
      cofactor_exponent_if_new_transfer_proved=str(adjusted),
      cofactor_lean_status='new transfer theorem not yet formalized',
      seconds=round(time.monotonic()-t0,3),
      certifier_sha256=hashlib.sha256((ROOT/'output/pdf/odd_pi_powers_notes/code/certify.py').read_bytes()).hexdigest())
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/f'{name}.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)

def main():
    a=argparse.ArgumentParser();a.add_argument('--case',choices=CASES)
    a.add_argument('--audit-archives',action='store_true')
    a.add_argument('--replay',nargs='+',choices=CASES,default=['L99'])
    args=a.parse_args();OUT.mkdir(parents=True,exist_ok=True)
    if args.audit_archives:audit_archives();return
    if args.case:child(args.case);return
    from bounded_lean import run_job
    accepted=F(42170551935,35026168)
    cofactor=accepted*F(184,186)
    exact=dict(status='exact arithmetic; cofactor theorem NOT yet Lean-formalized',
      accepted_P6_bound=str(accepted),cofactor_bound_if_new_transfer_proved=str(cofactor),
      decimal=float(cofactor),strict_target='1191.027',
      strict_comparison=cofactor<F('1191.027'))
    assert exact['strict_comparison']
    (OUT/'exact_p6_comparison.json').write_text(json.dumps(exact,indent=2),encoding='utf-8')
    print(json.dumps(exact),flush=True)
    for name in args.replay:
        code=run_job([sys.executable,str(Path(__file__).resolve()),'--case',name],
          ROOT,OUT/f'{name}.log',1536,240,
          env_overrides={'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'})
        if code:raise SystemExit(code)

if __name__=='__main__':main()
