"""Check an explicit, already topologically ordered P4 file list serially."""
from pathlib import Path
from datetime import datetime
import hashlib
import json
import subprocess
import sys
import time
from bounded_lean import available

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

workspace = Path(__file__).resolve().parent.parent
project = workspace/'formalization/OddPiPowers'
stamp = datetime.now().strftime('%Y%m%dT%H%M%S')
state_path = project/f'logs/p4-sequence-{stamp}.json'
state = dict(status='running', files=sys.argv[1:], completed=[], current=None)
def save():
    state_path.write_text(json.dumps(state, indent=2), encoding='utf-8')
save()
for i, filename in enumerate(sys.argv[1:]):
    state['current'] = filename; save()
    # Windows may take a moment to return resident pages after a child exits.
    # Wait for the existing launch threshold; never weaken it or launch early.
    time.sleep(2)
    begin=time.monotonic()
    while True:
        memory=available()
        if memory.free_phys >= 2560*2**20 and memory.free_commit >= 12288*2**20:
            break
        if time.monotonic()-begin > 45:
            state.update(status='resource_wait', exit_code=75); save()
            raise SystemExit('Launch threshold did not recover; nothing started.')
        time.sleep(1)
    log = f'logs/p4-{Path(filename).stem}-{stamp}.log'
    print(f'[{i+1}/{len(sys.argv)-1}] {filename}', flush=True)
    code = subprocess.call([sys.executable, str(workspace/'scripts/bounded_lean.py'),
        filename, '--emit', '--timeout', '300', '--log', log], cwd=workspace)
    if code:
        state.update(status='failed', exit_code=code, failed_log=log); save()
        if (project/log).exists():
            print((project/log).read_text(encoding='utf-8', errors='replace')[-7000:], flush=True)
        raise SystemExit(code)
    state['completed'].append(dict(file=filename, log=log,
        sha256=hashlib.sha256((project/filename).read_bytes()).hexdigest())); save()
state.update(status='completed', current=None); save()
print('All files passed; state=' + str(state_path), flush=True)
