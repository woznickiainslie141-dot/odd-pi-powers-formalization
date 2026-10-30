"""Integer local search (variable-neighbourhood descent + kicks) for E_k.

Pool of offsets 0..Tmax (zero weight = offset absent; exact, since the full
partition refines every sub-partition).  Moves:
  singles  nu_j += d, d in {-3,-2,-1,1,2,3}
  transfer nu_i += 1, nu_j -= 1          (also +1/-2, +2/-1)
  blocks   nu_[i..j] += d, d in {-1,+1}  (all intervals)
  zero     nu_j -> 0 (drop a layer)
usage: python localsearch.py k L a b T [kicks] [seed]
Writes ls_k{k}_L{L}.json (best found) and prints progress.
"""
import sys
import json
import time
import numpy as np
from common import build, eval_many, tmax_for


def neighbours(nu, classes):
    n = len(nu)
    C = []
    if "single" in classes:
        for j in range(n):
            for d in (-3, -2, -1, 1, 2, 3):
                v = nu.copy(); v[j] += d; C.append(v)
            if nu[j] > 0 and j > 0:
                v = nu.copy(); v[j] = 0; C.append(v)
    if "transfer" in classes:
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                for di, dj in ((1, 1), (1, 2), (2, 1)):
                    if nu[j] >= dj:
                        v = nu.copy(); v[i] += di; v[j] -= dj; C.append(v)
    if "block" in classes:
        for i in range(n):
            for j in range(i + 1, n):
                for d in (-1, 1):
                    v = nu.copy(); v[i:j + 1] += d; C.append(v)
    C = np.array(C)
    ok = (C.min(axis=1) >= 0) & (C[:, 0] >= 1)
    return C[ok]


def descend(k, data, nu, log, classes_seq=(("single",), ("transfer",), ("block",))):
    cur = eval_many(k, data, [nu])["E"][0]
    it = 0
    while True:
        improved = False
        for classes in classes_seq:
            C = neighbours(nu, classes)
            r = eval_many(k, data, C)
            i = int(np.argmin(r["E"]))
            if r["E"][i] < cur - 1e-9:
                nu, cur = C[i].copy(), float(r["E"][i])
                it += 1
                log(f"  it{it} [{classes[0]}] E={cur:.4f} m={int(r['m'][i])} nu={trim(nu)}")
                improved = True
                break
        if not improved:
            return nu, cur


def trim(nu):
    nz = np.nonzero(nu)[0]
    last = nz[-1] if len(nz) else 0
    return list(map(int, nu[:last + 1]))


def main():
    k, L, a, b, T = map(int, sys.argv[1:6])
    kicks = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    rng = np.random.default_rng(seed)
    Tmax = tmax_for(L)
    offs = tuple(range(Tmax + 1))
    data = build(L, offs)
    n = len(offs)
    nu = np.zeros(n, dtype=np.int64)
    nu[0] = a; nu[1:T + 1] = b
    t0 = time.time()
    logf = open(f"ls_k{k}_L{L}.log", "a", encoding="utf-8")

    def log(s):
        print(s, flush=True); logf.write(s + "\n"); logf.flush()

    log(f"== k={k} L={L} Tmax={Tmax} start a={a} b={b} T={T} kicks={kicks} seed={seed}")
    best_nu, best = descend(k, data, nu, log)
    log(f"descent done E={best:.4f} ({time.time()-t0:.0f}s) nu={trim(best_nu)}")
    save(k, L, Tmax, data, best_nu, best, t0)
    for kk in range(kicks):
        v = best_nu.copy()
        for _ in range(rng.integers(2, 6)):
            i, j = rng.integers(0, n, size=2)
            if v[j] > 0 and (j > 0 or v[0] > 1):
                v[i] += 1; v[j] -= 1
        v2, e2 = descend(k, data, v, lambda s: None)
        log(f"kick {kk}: E={e2:.4f} {'IMPROVED' if e2 < best - 1e-9 else ''}")
        if e2 < best - 1e-9:
            best_nu, best = v2, e2
            log(f"   new best nu={trim(best_nu)}")
            save(k, L, Tmax, data, best_nu, best, t0)
    save(k, L, Tmax, data, best_nu, best, t0)
    log(f"FINAL L={L} E={best:.4f} nu={trim(best_nu)}")


def save(k, L, Tmax, data, best_nu, best, t0):
    r = eval_many(k, data, [best_nu])
    out = dict(k=k, L=L, Tmax=Tmax, E=best, nu_full=list(map(int, best_nu)),
               offsets=[int(t) for t in np.nonzero(best_nu)[0]],
               counts=[int(x) for x in best_nu[np.nonzero(best_nu)[0]]],
               **{key: float(r[key][0]) for key in ("m", "D", "G", "D0", "G0", "gamma", "Y", "gap")},
               secs=time.time() - t0)
    out["ratio"] = (out["D"] + out["G"]) / out["gap"]
    with open(f"ls_k{k}_L{L}.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
