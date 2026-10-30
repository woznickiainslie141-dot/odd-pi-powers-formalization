"""Arb certification of explicit nested Pade rates and exact arc minima."""
from fractions import Fraction as F
from pathlib import Path
import json
from flint import arb,ctx
from search_multilayer_pade import cells

ctx.prec=256


def ball(q):
    q=F(q)
    return arb(q.numerator)/q.denominator


def certify(m,L,offsets,counts,upper,k=3):
    models,W,psi=cells(L,tuple(offsets))
    pieces=[]
    gamma=arb(0)
    for a,b,rows in models:
        v=min(sum(c*w for c,w in zip(counts,row)) for row in rows)
        if not v:
            continue
        assert a>0
        gamma+=v*(ball(b).digamma()-ball(a).digamma())/L
        pieces.append([str(a),str(b),v])
    c=[F(L-2*a,L) for a in offsets]
    theta=arb.pi()/2
    def saddle(Y):
        return 2*sum((nu*(ball(cc)/(2*Y)).atan()
                      for nu,cc in zip(counts,c)),arb(0))-theta
    lo,hi=F(1,100),F(2*(m+1))
    assert saddle(ball(lo))>0 and saddle(ball(hi))<0
    for _ in range(210):
        mid=(lo+hi)/2
        test=saddle(ball(mid))
        if test>0:
            lo=mid
        elif test<0:
            hi=mid
        else:
            break
    Y=arb(ball((lo+hi)/2),ball((hi-lo)/2))
    D0=sum((nu*(ball(cc)/2*((1+(2*Y/ball(cc))**2)/4).log()
                       +2*Y*(ball(cc)/(2*Y)).atan())
            for nu,cc in zip(counts,c)),arb(0))-theta*Y-m
    G0=m+sum((nu*ball(cc) for nu,cc in zip(counts,c)),arb(0))*arb(2).log()
    D=D0+gamma
    G=G0-gamma
    gap=D-(k-1)*G
    assert gap>0 and G>0
    E=m*(D+G)/gap
    assert E<arb(upper)
    return {"k":k,"m":m,"L":L,"offsets":list(offsets),"counts":counts,
            "Y_interval":str(Y),"D0":str(D0),"G0":str(G0),
            "gamma":str(gamma),"D":str(D),"G":str(G),
            "gap":str(gap),"E":str(E),"certified_strict_upper":upper,
            "nonzero_gamma_cells":pieces}


if __name__=="__main__":
    rows=[
        certify(255,14,[0,1],[128,128],"1762.609"),
        certify(199,39,list(range(7)),[80,20,20,20,20,20,20],"1282.034"),
        certify(186,69,list(range(12)),[66]+[11]*11,"1203.973")
    ]
    data={"arithmetic":"Arb 256 bits; exact rational arc arrangement",
          "scope":"Certifies rate expressions; proof of their applicability is separate.",
          "rows":rows}
    Path(__file__).with_name("nested_pade_certificate_2026-10-27.json").write_text(
        json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps([{k:v for k,v in r.items() if k!="nonzero_gamma_cells"}
                      for r in rows],indent=2))
