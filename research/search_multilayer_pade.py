"""Exact arc partitions with a bounded floating-point multilayer search."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json
import numpy as np
from scipy.special import digamma


@lru_cache(None)
def cells(L, offsets):
    slopes=sorted(set((0,)+offsets+tuple(L-a for a in offsets)))
    ds=set(abs(s-t) for s in slopes for t in slopes if s != t)
    cuts=sorted({F(k,d) for d in ds for k in range(d+1)})
    models=[]
    for a,b in zip(cuts,cuts[1:]):
        z=(a+b)/2
        ends=sorted({F(0),F(1)}|{(s*z)%1 for s in slopes})
        rows=[]
        for u,v in zip(ends,ends[1:]):
            y=(u+v)/2
            row=tuple(((L-2*t)*z).__floor__()-(y-t*z).__floor__()
                      -((L-t)*z-y).__floor__() for t in offsets)
            assert all(w in (0,1) for w in row)
            if row not in rows:
                rows.append(row)
        models.append((a,b,rows))
    maxrows=max(len(r) for a,b,r in models)
    W=np.array([r+[r[-1]]*(maxrows-len(r)) for a,b,r in models],dtype=float)
    psi=np.array([0 if a==0 else float(digamma(float(b))-digamma(float(a)))
                  for a,b,r in models])/L
    return models,W,psi


def evaluate(m,L,offsets,counts):
    models,W,psi=cells(L,tuple(offsets))
    counts=np.asarray(counts,dtype=float)
    assert abs(counts.sum()-(m+1)) < 1e-7
    mins=np.einsum("cij,j->ci",W,counts).min(axis=1)
    assert mins[0] == 0
    gamma=psi@mins
    c=1-2*np.array(offsets)/L
    Y=(counts@c)/(np.pi/2)
    for _ in range(6):
        f=2*(counts@np.arctan(c/(2*Y)))-np.pi/2
        fp=-counts@(c/(Y*Y+c*c/4))
        Y-=f/fp
    D0=counts@(c/2*np.log((1+(2*Y/c)**2)/4)+2*Y*np.arctan(c/(2*Y)))-np.pi/2*Y-m
    G0=m+(counts@c)*np.log(2)
    gap=D0-2*G0+3*gamma
    return {"m":int(m),"L":L,"offsets":list(offsets),"counts":list(map(int,counts)),
            "D0":float(D0),"G0":float(G0),"gamma":float(gamma),
            "E":float(m*(D0+G0)/gap) if gap>0 else None}


if __name__=="__main__":
    from scipy.optimize import minimize_scalar, differential_evolution
    results=[]
    claimed=evaluate(245,39,range(5),[50,49,49,49,49])
    print("Claimed-parameter reconstruction:",json.dumps(claimed),flush=True)
    for J in range(3,8):
        for L in range(max(12,2*J+1),66):
            offsets=tuple(range(J))
            models,W,psi=cells(L,offsets)
            c=1-2*np.array(offsets)/L
            # Equal proportions: gamma scales exactly with M.
            gamma_per_M=float(psi@W.mean(axis=2).min(axis=1))
            def obj(m):
                M=m+1
                weights=np.ones(J)*M/J
                Y=(weights@c)/(np.pi/2)
                for _ in range(4):
                    Y-=(2*(weights@np.arctan(c/(2*Y)))-np.pi/2)/(-weights@(c/(Y*Y+c*c/4)))
                D0=weights@(c/2*np.log((1+(2*Y/c)**2)/4)+2*Y*np.arctan(c/(2*Y)))-np.pi/2*Y-m
                G0=m+(weights@c)*np.log(2)
                gap=D0-2*G0+3*M*gamma_per_M
                return m*(D0+G0)/gap if gap>0 else 1e8
            opt=minimize_scalar(obj,bounds=(120,450),method="bounded")
            for m in range(round(opt.x)-2,round(opt.x)+3):
                counts=[(m+1)//J+(j<(m+1)%J) for j in range(J)]
                results.append(evaluate(m,L,offsets,counts))
        print("Completed levels",J,flush=True)
    results=[r for r in results if r["E"] is not None]
    results.sort(key=lambda d:d["E"])
    seed=results[0]
    # Optimize the integer multiplicities at the best offsets found.
    J=len(seed["offsets"])
    def int_obj(raw):
        counts=np.maximum(1,np.rint(raw)).astype(int)
        r=evaluate(int(sum(counts)-1),seed["L"],seed["offsets"],counts)
        return r["E"] if r["E"] is not None else 1e8
    opt=differential_evolution(int_obj,[(1,100)]*J,popsize=8,maxiter=100,
                               seed=20261027,polish=False,tol=1e-7)
    counts=np.maximum(1,np.rint(opt.x)).astype(int)
    refined=evaluate(int(sum(counts)-1),seed["L"],seed["offsets"],counts)
    data={"floating_search_only":True,"scope":{"levels":[3,7],"L_max":65,
          "offsets":"0,1,...,J-1; near-equal multiplicities; one weight refinement"},
          "attachment_five_layer_reconstruction":claimed,"best":results[:10],
          "refined":refined}
    Path(__file__).with_name("multilayer_pade_search_2026-10-27.json").write_text(
        json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(data,indent=2),flush=True)
