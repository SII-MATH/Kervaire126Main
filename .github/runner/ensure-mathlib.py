#!/usr/bin/env python3
"""Fetch imported dependency artifacts once per environment and import set."""
import hashlib
import json
import os
from pathlib import Path
import subprocess


def artifacts_present(root, modules):
    packages = root / '.lake/packages'
    bases = [p / '.lake/build/lib/lean' for p in packages.iterdir() if p.is_dir()]
    return all(any((base / (name.replace('.', '/') + '.olean')).is_file()
                   for base in bases) for name in modules)


def ensure(root, run=subprocess.run):
    modules = subprocess.check_output(['lake', 'env', 'python3', 'scripts/mathlib-cache-roots.py'],
                                      cwd=root, text=True).splitlines()
    key = hashlib.sha256(json.dumps({
        'toolchain': (root / 'lean-toolchain').read_text(),
        'manifest': (root / 'lake-manifest.json').read_text(),
        'imports': modules,
    }, sort_keys=True).encode()).hexdigest()
    marker = root / '.lake/packages' / ('.runner-mathlib-' + key)
    if marker.is_file() and artifacts_present(root, modules):
        print('Imported Mathlib artifacts already verified for this environment/import set', flush=True)
        return
    if modules:
        run(['lake', 'exe', 'cache', 'get', *modules], cwd=root, check=True)
        if not artifacts_present(root, modules):
            raise ValueError('Dependency cache completed without all imported artifacts')
    marker.write_text(key + '\n')
    print('Recorded successful dependency cache for this import set', flush=True)


if __name__ == '__main__':
    ensure(Path(os.environ['GITHUB_WORKSPACE']))
