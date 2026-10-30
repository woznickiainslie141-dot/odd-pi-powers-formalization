"""Three-level family nu=(a, b x T1, c x T2) (c != b; c may be larger or smaller),
plus 'interleaved' family nu=(a, then T layers of b with every p-th layer b+1).
Searched around the best two-level point of scan2.  Float search only.
usage: python scan3.py k L a0 b0 T0
"""
import sys
import json
import time
import numpy as np
from common import build, eval_many, tmax_for


def main():
    k, L, a0, b0, T0 = map(int, sys.argv[1:6])
    Tmax = tmax_for(L)
    offs = tuple(range(Tmax + 1))
    data = build(L, offs)
    n = len(offs)
    t0 = time.time()
    cols, meta = [], []
    A = range(max(1, a0 - 8), a0 + 9)
    for b in range(max(1, b0 - 1), b0 + 2):
        for c in range(1, b0 + 4):
            if c == b:
                continue
            for T1 in range(max(1, T0 // 3), T0 + 6):
                for T2 in range(1, Tmax - T1 + 1):
                    if abs(b * T1 + c * T2 - b0 * T0) > 0.25 * b0 * T0:
                        continue
                    for a in A:
                        nu = np.zeros(n); nu[0] = a; nu[1:T1 + 1] = b; nu[T1 + 1:T1 + T2 + 1] = c
                        cols.append(nu); meta.append(("3lev", a, b, T1, c, T2))
    # interleaved: b with every p-th layer replaced by b+1 (p=2..6) or b-1
    for b in range(max(1, b0 - 1), b0 + 2):
        for d in (1, -1):
            if b + d < 1:
                continue
            for p in range(2, 7):
                for ph in range(p):
                    for T in range(max(1, T0 - 10), min(Tmax, T0 + 12) + 1):
                        for a in A:
                            nu = np.zeros(n); nu[0] = a; nu[1:T + 1] = b
                            idx = np.arange(1, T + 1)
                            nu[idx[(idx % p) == ph]] = b + d
                            cols.append(nu); meta.append(("intl", a, b, d, p, ph, T))
    print(f"L={L}: {len(cols)} candidates", flush=True)
    r = eval_many(k, data, cols)
    order = np.argsort(r["E"])
    top = []
    for i in order[:15]:
        nu = cols[i]
        nz = np.nonzero(nu)[0]
        top.append(dict(E=float(r["E"][i]), meta=meta[i], m=int(r["m"][i]),
                        nu=list(map(int, nu[:nz[-1] + 1]))))
    res = dict(k=k, L=L, secs=time.time() - t0, ncols=len(cols), top=top)
    with open(f"scan3_k{k}_results.jsonl", "a", encoding="utf-8") as f:
        f.write(json.dumps(res) + "\n")
    for t in top[:6]:
        print(f"  E={t['E']:.4f} m={t['m']} {t['meta']}", flush=True)
    print(f"({res['secs']:.0f}s)")


if __name__ == "__main__":
    main()
