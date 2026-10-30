"""Run several certificates in one process (shares the exact arc-partition cache).
usage: python cert_batch.py jobs.json   [{k,L,nu,upper,tag}, ...]"""
import sys, json, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "code"))
from certify import certify  # noqa: E402
jobs = json.load(open(sys.argv[1]))
for j in jobs:
    t0 = time.time()
    offsets = list(range(len(j["nu"])))
    row, _ = certify(j["k"], j["L"], offsets, j["nu"], j["upper"])
    row.pop("nonzero_merged_cells")
    row["seconds"] = round(time.time() - t0, 1)
    Path(__file__).with_name(f"cert_{j['tag']}.json").write_text(json.dumps(row, indent=1) + "\n", encoding="utf-8")
    print(f"{j['tag']}: k={j['k']} L={j['L']} T={len(j['nu'])-1} m={row['m']} nu={j['nu'][:2]}..{j['nu'][-1]}", flush=True)
    print("   E =", row["E"], "<", j["upper"], " CERTIFIED", f"({row['seconds']}s)", flush=True)
