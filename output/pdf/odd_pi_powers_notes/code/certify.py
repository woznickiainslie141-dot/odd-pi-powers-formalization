"""Standalone certificates for the manuscript; requires only python-flint.

Arc endpoints and minima are exact Fractions/integers. All transcendental
comparisons use Arb balls, including signs in monotone root bisection.
The analytic proof is in the manuscript, not in this finite computation.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json
from flint import arb, ctx

ctx.prec = 256
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)


def ball(q):
    q = F(q)
    return arb(q.numerator) / q.denominator


def floor(q):
    return q.numerator // q.denominator


@lru_cache(None)
def arc_partition(L, offsets):
    """Return all rational cells and all distinct W-vectors per cell."""
    slopes = sorted({0, *offsets, *(L-t for t in offsets)})
    diffs = {abs(a-b) for a in slopes for b in slopes if a != b}
    cuts = sorted({F(k,d) for d in diffs for k in range(d+1)})
    cells = []
    for a,b in zip(cuts,cuts[1:]):
        z = (a+b)/2
        ends = sorted({F(0), F(1), *((t*z) % 1 for t in slopes)})
        rows = set()
        for u,v in zip(ends,ends[1:]):
            y = (u+v)/2
            row = tuple(floor((L-2*t)*z)-floor(y-t*z)
                        -floor((L-t)*z-y) for t in offsets)
            assert all(w in (0,1) for w in row)
            rows.add(row)
        cells.append((a,b,tuple(sorted(rows))))
    return tuple(cells)


def divisor_rate(L, offsets, counts):
    gamma = arb(0)
    pieces = []
    for a,b,rows in arc_partition(L,tuple(offsets)):
        v = min(sum(nu*w for nu,w in zip(counts,row)) for row in rows)
        if v == 0:
            continue
        assert a > 0
        gamma += v*(ball(b).digamma()-ball(a).digamma())/L
        if pieces and pieces[-1][1] == str(a) and pieces[-1][2] == v:
            pieces[-1][1] = str(b)
        else:
            pieces.append([str(a),str(b),v])
    return gamma,pieces


def certify(k,L,offsets,counts,upper):
    assert k >= 3 and k % 2 == 1
    assert offsets[0] == 0 and list(offsets) == sorted(set(offsets))
    assert 2*offsets[-1] < L and min(counts) >= 1
    assert len(offsets) == len(counts)
    M = sum(counts)
    m = M-1
    assert m >= 1
    gamma,pieces = divisor_rate(L,offsets,counts)
    lengths = [F(L-2*t,L) for t in offsets]
    theta = arb.pi()/2

    def equation(Y):
        return 2*sum((nu*(ball(c)/(2*Y)).atan()
                      for c,nu in zip(lengths,counts)),arb(0))-theta

    lo,hi = F(1,2),F(2*M)
    assert equation(ball(lo)) > 0 and equation(ball(hi)) < 0
    for _ in range(210):
        mid = (lo+hi)/2
        v = equation(ball(mid))
        if v > 0:
            lo = mid
        elif v < 0:
            hi = mid
        else:
            raise ArithmeticError("Raise Arb precision for this root.")
    Y = arb(ball((lo+hi)/2),ball((hi-lo)/2))
    D0 = sum((nu*(ball(c)/2*((1+(2*Y/ball(c))**2)/4).log()
                  +2*Y*(ball(c)/(2*Y)).atan())
              for c,nu in zip(lengths,counts)),arb(0))-theta*Y-m
    G0 = m+sum((nu*ball(c) for c,nu in zip(lengths,counts)),arb(0))*arb(2).log()
    D,G = D0+gamma,G0-gamma
    gap = D-(k-1)*G
    assert G > 0 and gap > 0
    E = m*(D+G)/gap
    assert E < arb(upper)
    return {
        "k":k, "m":m, "L":L, "offsets":list(offsets),
        "counts":list(counts), "Y":str(Y),
        "D0":str(D0), "G0":str(G0), "gamma":str(gamma),
        "D":str(D), "G":str(G), "gap":str(gap), "E":str(E),
        "strict_upper":upper, "nonzero_merged_cells":pieces,
        "critical_cell_count":len(arc_partition(L,tuple(offsets))),
    }, (Y,D0,G0,gamma,D,G,gap,E)


def check_discrete_minima():
    """Independent comparison with all integer pole locations at n=345."""
    L,n = 69,345
    offsets = tuple(range(12))
    counts = [66]+[11]*11
    cells = arc_partition(L,offsets)
    primes = [p for p in range(19,n+1)
              if all(p % d for d in range(2,int(p**0.5)+1))]
    checked = positive = 0
    for p in primes:
        z = F(n//L,p) % 1
        cell = next(((a,b,r) for a,b,r in cells if a<z<b),None)
        if cell is None:
            continue
        a,b,rows = cell
        f = min(sum(nu*w for nu,w in zip(counts,row)) for row in rows)
        actual = min(sum(
            nu*((n-2*t*(n//L))//p-(ell-t*(n//L))//p
                -(n-t*(n//L)-ell)//p)
            for nu,t in zip(counts,offsets)) for ell in range(n+1))
        assert actual >= f
        checked += 1
        positive += f > 0
    return {"n":n,"primes_checked":checked,
            "primes_with_positive_lower_bound":positive}


def main():
    configurations = [
        ("two_layer",3,14,[0,1],[128,128],"1762.609"),
        ("seven_layer",3,39,list(range(7)),[80]+[20]*6,"1282.034"),
        ("twelve_pi3",3,69,list(range(12)),[66]+[11]*11,"1203.973"),
        ("twelve_pi5",5,69,list(range(12)),[1554]+[259]*11,"42461"),
        ("twelve_pi7",7,69,list(range(12)),[35226]+[5871]*11,"1272103"),
        ("twelve_pi9",9,69,list(range(12)),[788124]+[131354]*11,"35398937"),
    ]
    rows = []
    raw_rates = {}
    for name,k,L,offsets,counts,upper in configurations:
        row,rates = certify(k,L,offsets,counts,upper)
        row["name"] = name
        rows.append(row)
        raw_rates[name] = rates
        print(name, "E =",row["E"],"<",upper,flush=True)
    gamma_star,pieces = divisor_rate(69,list(range(12)),[6]+[1]*11)
    S = arb(347)/23
    moment = sum((nu*ball(F(69-2*t,69))*ball(F(69-2*t,69)).log()
                  for t,nu in enumerate([6]+[1]*11)),arb(0))
    gstar = 17+S*arb(2).log()-gamma_star
    dstar = S*(S/(arb.pi()/2)).log()-moment-17+gamma_star
    rho = (gstar/S).exp()
    assert gstar > 23
    assert rho < arb("4.693440")
    root_free_checks = []
    for row in rows:
        if row["L"] != 69:
            continue
        k,s = row["k"],row["counts"][1]
        lower_D = s*(S*arb(s).log()+dstar)+1-(arb.pi()/2)**2/(12*s*S)
        G = s*gstar-1
        low_gap = lower_D-(k-1)*G
        assert raw_rates[row["name"]][4] > lower_D
        assert low_gap > 0
        upper_E = row["m"]*(lower_D+G)/low_gap
        assert upper_E > raw_rates[row["name"]][-1]
        root_free_checks.append({"k":k,"s":s,"lower_D":str(lower_D),
                                 "gap":str(low_gap),"E":str(upper_E)})
    data = {
        "arithmetic":"Arb, 256 bits; exact rational cells and integer minima",
        "scope":"Numerical comparisons, not a proof of analytic applicability",
        "rows":rows,
        "base_shape":{
            "S":"347/23", "gamma_star":str(gamma_star),
            "gstar":str(gstar), "dstar":str(dstar), "rho":str(rho),
            "nonzero_merged_cells":pieces,
        },
        "discrete_floor_check":check_discrete_minima(),
        "root_free_checks_at_selected_scales":root_free_checks,
    }
    (DATA/"certificates.json").write_text(
        json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print("Base gamma:",gamma_star,"rho:",rho,flush=True)
    print("First base cells:",pieces[:8],flush=True)
    print("All certified comparisons passed.",flush=True)


if __name__ == "__main__":
    main()
