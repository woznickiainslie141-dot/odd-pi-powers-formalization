"""Fetch only pinned PNT Mathlib dependencies under the existing job guard.

Downloads and decompression are separate jobs, avoiding the cache CLI's
overlapping curl/decompression pipeline. No Lean compilation is performed.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
from bounded_lean import run_job, other_compilers

workspace = Path(__file__).resolve().parent.parent
project = workspace / 'formalization/OddPiPowers'
mathlib = project / '.lake/packages/mathlib'
mode = sys.argv[1] if len(sys.argv) == 2 else ''
if mode not in ('download', 'decompress'):
    raise SystemExit('Usage: bounded_pnt_cache.py download|decompress')
if other_compilers():
    raise SystemExit('Another compiler exists; cache work will not overlap it.')
elan = shutil.which('elan')
lake = Path(subprocess.check_output([elan, 'which', 'lake'], cwd=project, text=True).strip())
git = shutil.which('git')
git_exec = Path(subprocess.check_output([git, '--exec-path'], text=True).strip())
git_bin = git_exec.parent.parent / 'bin'
package_roots = [p for p in (project/'.lake/packages').iterdir() if p.is_dir()]
roots = set()
for f in (project/'OddPiPowers/Vendor/PNT').rglob('*.lean'):
    for name in re.findall(r'^import\s+(\S+)', f.read_text(encoding='utf-8'), re.M):
        if name.startswith('Mathlib.'):
            roots.add(name)
cache_dir = workspace/'tmp/p4-mathlib-cache'
cache_dir.mkdir(parents=True, exist_ok=True)
env = {
    'PATH': str(lake.parent) + os.pathsep + str(git_bin) + os.pathsep + os.environ['PATH'],
    'LEAN_SRC_PATH': os.pathsep.join(map(str, [project, *package_roots])),
    'MATHLIB_CACHE_DIR': str(cache_dir),
    'RAYON_NUM_THREADS': '1',
}
binary = mathlib/'.lake/build/bin/cache.exe'
if not binary.is_file():
    raise SystemExit('Existing cache executable is unavailable; do not build it unguarded.')
# Second get should have no downloads left. If cache overlaps subprocesses,
# the unchanged two-process job cap refuses them rather than allowing a burst.
command = [str(binary), 'get-' if mode == 'download' else 'get', *sorted(roots)]
log = project/('logs/p4-pnt-cache-' + mode + '.log')
print(f'{mode}: {len(roots)} pinned Mathlib import roots', flush=True)
raise SystemExit(run_job(command, project, log, 6144, 300, env_overrides=env))
