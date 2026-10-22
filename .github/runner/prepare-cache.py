#!/usr/bin/env python3
"""Keep local incremental caches separate for each locked Lean environment."""
import hashlib
import os
from pathlib import Path
import importlib.util


def environment_key(root):
    digest = hashlib.sha256()
    for name in ('lean-toolchain', 'lake-manifest.json'):
        digest.update(name.encode() + b'\0' + (root / name).read_bytes() + b'\0')
    return digest.hexdigest()


def build_fingerprint(root):
    spec = importlib.util.spec_from_file_location('ci_inputs', root / 'scripts/ci-cache.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.build_inputs(root)['fingerprint']


def prepare(root, cache, fingerprint=None):
    lake = root / '.lake'
    expected = environment_key(root)
    cache = cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    environment = cache / expected
    target = environment if fingerprint is None else environment / 'inputs' / fingerprint
    if fingerprint is not None and (len(fingerprint) != 64 or any(c not in '0123456789abcdef' for c in fingerprint)):
        raise ValueError('Invalid build input fingerprint')
    if target.is_symlink():
        raise ValueError('Persistent cache environment must be an independent directory')
    if lake.is_symlink():
        actual = lake.resolve()
        relative = actual.relative_to(cache) if actual.is_relative_to(cache) else Path('invalid')
        parts = relative.parts
        valid = (len(parts) == 1 or (len(parts) == 3 and parts[1] == 'inputs'))
        hashes = parts if len(parts) == 1 else (parts[0], parts[-1])
        if not valid or any(len(p) != 64 or any(c not in '0123456789abcdef' for c in p) for p in hashes):
            raise ValueError('CI .lake cannot point outside the dedicated environment cache')
        if actual != target:
            lake.unlink()
    elif lake.exists():
        # Migrate the initial independently seeded directory out of checkout.
        import time
        marker = lake / 'runner-environment'
        old = marker.read_text().strip() if marker.exists() else 'unclassified'
        if old == expected and not target.exists():
            lake.rename(target)
        else:
            lake.rename(cache / ('previous-' + str(time.time_ns())))
    target.mkdir(parents=True, exist_ok=True)
    if fingerprint is not None:
        packages = environment / 'packages'
        packages.mkdir(exist_ok=True)
        if not (target / 'packages').exists():
            (target / 'packages').symlink_to(packages, target_is_directory=True)
        (target / 'runner-build-inputs').write_text(fingerprint + '\n')
    (target / 'runner-environment').write_text(expected + '\n')
    if not lake.is_symlink():
        lake.symlink_to(target, target_is_directory=True)
    print('Persistent CI cache environment:', expected)
    restore = not (target / 'build').exists()
    if output := os.environ.get('GITHUB_OUTPUT'):
        with open(output, 'a') as stream:
            stream.write('restore_release=' + str(restore).lower() + '\n')
    print('Project cache inputs:', fingerprint or 'legacy environment')
    print('Exact project cache needs Release restore:', restore)
    return target


if __name__ == '__main__':
    root = Path(os.environ['GITHUB_WORKSPACE'])
    prepare(root, Path.home() / 'cache/environments', build_fingerprint(root))
