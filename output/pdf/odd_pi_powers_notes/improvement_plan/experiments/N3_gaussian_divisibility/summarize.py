"""Summarize results/*.jsonl: excess of evaluated gcds over coefficient content, by prime range."""
import json, sys, math
from pathlib import Path
HERE = Path(__file__).resolve().parent
KEYS = ["p2", "small", "mid", "large", "beyond"]


def load(name):
    return [json.loads(l) for l in open(HERE / "results" / f"{name}.jsonl")]


def table(name, every=1):
    rs = load(name)
    r0 = rs[0]
    print(f"### {name}: L={r0['L']} t={r0['offsets']} nu={r0['nu']} M={r0['M']} gamma(formula)={r0['gamma_formula']:.4f}")
    print(" n   | Pi/n   coef/n | mat-coef: tot  p2   small  mid  large | minrow-coef: tot  p2   small  mid  large | shiftrow-coef | maxent/n")
    for r in rs[::every]:
        n = r["n"]
        mc = {k: (r["logmat_by"][k] - r["logcoef_by"][k]) / n for k in KEYS}
        h = min(range(r["M"]), key=lambda h: r["logrow"][h])
        rc = {k: (r["logrow_by"][h][k] - r["logcoef_by"][k]) / n for k in KEYS}
        sh = (min(r["euclid_logrow_shift"]) - r["logcoef"]) / n
        print(f"{n:5d}| {r['logPi']/n:.4f} {r['logcoef']/n:.4f} | {sum(mc.values()):.4f} {mc['p2']:.4f} {mc['small']:.4f} {mc['mid']:.4f} {mc['large']:.4f} "
              f"| {sum(rc.values()):.4f} {rc['p2']:.4f} {rc['small']:.4f} {rc['mid']:.4f} {rc['large']:.4f} | {sh:.4f} | {r['max_entry_log']/n:.3f}")


if __name__ == "__main__":
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    for name in sys.argv[1].split(","):
        table(name, every)
