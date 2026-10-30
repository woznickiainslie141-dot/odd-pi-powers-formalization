import os
import time
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "4")
import numpy as np  # noqa: E402
from cells import build as _build, E_batch  # noqa: E402,F401


def _retry(fn, *a, tries=30, **kw):
    for i in range(tries):
        try:
            return fn(*a, **kw)
        except MemoryError:
            print(f"[MemoryError, retry {i+1} in 20s]", flush=True)
            time.sleep(20)
    return fn(*a, **kw)


def build(L, offs, verbose=False):
    return _retry(_build, L, offs, verbose=verbose)


def tmax_for(L):
    return min(int(np.ceil(0.36 * L)) + 3, (L - 1) // 2)


def eval_many(k, data, cols, chunk=None):
    """cols: list/array of nu vectors (each length n_off). Returns dict of arrays."""
    cols = np.asarray(cols, dtype=np.float64)
    if chunk is None:
        chunk = int(max(16, min(1024, 2.5e7 / data["R"].shape[0])))
    out = {}
    s = 0
    fails = 0
    while s < len(cols):
        try:
            r = E_batch(k, data, cols[s:s + chunk].T)
        except MemoryError:
            fails += 1
            if fails > 60:
                raise
            chunk = max(8, chunk // 2)
            print(f"[MemoryError in eval, chunk->{chunk}, wait 15s]", flush=True)
            time.sleep(15)
            continue
        for key in ("E", "m", "D", "G", "D0", "G0", "gamma", "Y", "gap"):
            out.setdefault(key, []).append(np.asarray(r[key]))
        s += chunk
    return {k_: np.concatenate(v) for k_, v in out.items()}
