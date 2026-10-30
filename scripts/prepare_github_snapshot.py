"""Copy the current working materials into a new source-only Git snapshot.

Never deletes or changes source files, Git metadata, caches or toolchains.
The destination must not exist and must be outside the source workspace.
"""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import argparse
import hashlib
import json
import os
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {'.git', '.lake', '__pycache__', 'node_modules', '.venv', 'venv'}
SKIP_SUFFIXES = {'.pyc', '.olean', '.ilean', '.trace', '.ltar'}
SKIP_PATHS = {'tmp/p4-mathlib-cache', 'tmp/lean-4.35.0-windows.tar.zst'}
TOKEN_PATTERNS = [
    re.compile(rb'gh[pousr]_[A-Za-z0-9]{30,}'),
    re.compile(rb'github_pat_[A-Za-z0-9_]{50,}'),
    re.compile(rb'sk-[A-Za-z0-9_-]{40,}'),
    re.compile(rb'AKIA[A-Z0-9]{16}'),
    re.compile(rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----'),
]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('destination', type=Path)
    parser.add_argument('--snapshot-date', default=None,
                        help='Date label; defaults to the current date in Hong Kong.')
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists() or destination == ROOT or ROOT in destination.parents:
        raise SystemExit('Destination must be new and outside the source workspace.')
    included, excluded, flagged = [], [], []
    for base, dirs, files in os.walk(ROOT, followlinks=False):
        for directory in list(dirs):
            path = Path(base) / directory
            relative = path.relative_to(ROOT).as_posix()
            if directory in SKIP_DIRS or relative in SKIP_PATHS or path.is_symlink():
                dirs.remove(directory)
                excluded.append({'path': relative, 'reason': 'metadata/cache or linked directory'})
        for name in files:
            path = Path(base) / name
            relative = path.relative_to(ROOT).as_posix()
            if relative in SKIP_PATHS or path.suffix.lower() in SKIP_SUFFIXES:
                excluded.append({'path': relative, 'reason': 'reconstructible build/installer artifact'})
                continue
            if name.startswith('.env') or path.suffix.lower() in {'.pem', '.key', '.pfx'}:
                flagged.append(relative)
                continue
            if path.stat().st_size >= 95 * 1024 * 1024:
                raise SystemExit(f'Unexpected oversized source file: {relative}')
            content = path.read_bytes()
            if any(pattern.search(content) for pattern in TOKEN_PATTERNS):
                flagged.append(relative)
            included.append((path, relative, len(content), hashlib.sha256(content).hexdigest()))
    if flagged:
        # Never print the matching value, even to a local execution log.
        print(json.dumps({'credential_scan_flagged_paths': flagged}, indent=2))
        raise SystemExit('Resolve flagged paths before creating a snapshot.')
    destination.mkdir(parents=True)
    for source, relative, _, _ in included:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    manifest = {
        'date': args.snapshot_date or datetime.now(timezone(timedelta(hours=8))).date().isoformat(),
        'scope': 'Current working-tree research archive; dated acceptance reports and README define the proved scope',
        'git_history': 'New snapshot; nested Git metadata and histories excluded',
        'credential_pattern_scan': 'No matches for the implemented high-confidence patterns',
        'included_file_count': len(included),
        'included_bytes': sum(item[2] for item in included),
        'excluded': sorted(excluded, key=lambda item: item['path']),
        'files': [{'path': relative, 'bytes': size, 'sha256': digest}
                  for _, relative, size, digest in sorted(included, key=lambda item: item[1])],
    }
    (destination / 'SNAPSHOT_MANIFEST.json').write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    for _, relative, _, digest in included:
        if hashlib.sha256((destination / relative).read_bytes()).hexdigest() != digest:
            raise SystemExit(f'Copy hash mismatch: {relative}')
    print(json.dumps({'destination': str(destination), 'files': len(included),
                      'bytes': manifest['included_bytes'], 'copy_hashes': 'all verified',
                      'credential_scan': 'no implemented-pattern matches'}, indent=2))


if __name__ == '__main__':
    main()
