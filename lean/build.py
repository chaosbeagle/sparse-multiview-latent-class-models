#!/usr/bin/env python3
"""Verify pinned inputs and run the full proof workflow in a new private directory."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def source_hashes(root):
    return {p.relative_to(root).as_posix(): digest(p) for p in root.rglob('*.lean')
            if '.lake' not in p.relative_to(root).parts}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--packages', required=True, type=Path)
    parser.add_argument('--work', type=Path)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    tc, pk = args.toolchain.resolve(), args.packages.resolve()
    expected = json.loads((HERE / 'SOURCE_SHA256.json').read_text())
    if source_hashes(HERE) != expected:
        raise SystemExit('Lean source inventory mismatch')
    compiler = tc / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    version = subprocess.check_output([str(compiler), '--version'], text=True).strip()
    if 'version 4.32.0,' not in version or '8c9756b28d64dab099da31a4c09229a9e6a2ef35' not in version:
        raise SystemExit('Pinned compiler version/commit mismatch: ' + version)
    env = {**os.environ, 'GIT_OPTIONAL_LOCKS': '0'}
    pins = json.loads((HERE / 'dependency-pins.json').read_text())['packages']
    for pin in pins:
        p = pk / pin['name']
        actual = subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'], env=env, text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(p), 'status', '--porcelain', '--untracked-files=no'], env=env, text=True)
        if actual != pin['rev'] or dirty:
            raise SystemExit('Dependency revision/cleanliness mismatch: ' + pin['name'])
        if pin['name'] == 'mathlib' and not (p / '.lake/build/lib/lean').is_dir():
            raise SystemExit('Compiled dependency artifacts missing: ' + pin['name'])
    print(f'PASS: {len(expected)} source hashes; pinned Lean commit; {len(pins)} clean dependency pins.', flush=True)
    if args.verify_only:
        print('Identity checks only; no new proof compilation or axiom audit.')
        return 0
    if os.name != 'posix':
        raise SystemExit('Full workflow requires POSIX (Linux/macOS/WSL).')
    if args.work is None:
        parser.error('--work is required unless --verify-only is used')
    work = args.work.resolve()
    if work.exists() or args.work.is_symlink():
        raise SystemExit('Work must not already exist or be a symlink')
    for protected in (HERE.parent.resolve(), tc, pk):
        if work == protected or protected in work.parents or work in protected.parents:
            raise SystemExit('Work must be separate from repository, toolchain and dependencies')
    shutil.copytree(HERE, work, ignore=shutil.ignore_patterns('.lake', 'build_logs', '__pycache__'))
    assert source_hashes(work) == expected
    env.update(LEAN_TOOLCHAIN=str(tc), LEAN_PACKAGES=str(pk))
    started = time.monotonic()
    with (work / 'full_build.log').open('w') as log:
        result = subprocess.run(['bash', 'leancheck.sh', '--lake', 'build'], cwd=work,
                                env=env, stdout=log, stderr=subprocess.STDOUT)
    unchanged = source_hashes(work) == expected
    record = {'exit_code': result.returncode, 'source_identity_preserved': unchanged,
              'elapsed_seconds': time.monotonic() - started,
              'status': 'PASS' if result.returncode == 0 and unchanged else 'FAIL',
              'shared_dependencies_modified': False, 'log': 'full_build.log'}
    (work / 'REBUILD_RESULT.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
    return 0 if record['status'] == 'PASS' else (result.returncode or 1)

if __name__ == '__main__':
    sys.exit(main())
