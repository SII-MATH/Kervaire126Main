#!/usr/bin/env python3
"""Keep local incremental caches separate for each locked Lean environment."""
import hashlib
import os
from pathlib import Path


def environment_key(root):
    digest = hashlib.sha256()
    for name in ('lean-toolchain', 'lake-manifest.json'):
        digest.update(name.encode() + b'\0' + (root / name).read_bytes() + b'\0')
    return digest.hexdigest()


def prepare(root, cache):
    lake = root / '.lake'
    expected = environment_key(root)
    cache = cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    target = cache / expected
    if target.is_symlink():
        raise ValueError('Persistent cache environment must be an independent directory')
    if lake.is_symlink():
        actual = lake.resolve()
        if actual.parent != cache or len(actual.name) != 64 or any(c not in '0123456789abcdef' for c in actual.name):
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
    target.mkdir(exist_ok=True)
    (target / 'runner-environment').write_text(expected + '\n')
    if not lake.is_symlink():
        lake.symlink_to(target, target_is_directory=True)
    print('Persistent CI cache environment:', expected)


if __name__ == '__main__':
    prepare(Path(os.environ['GITHUB_WORKSPACE']), Path.home() / 'cache/environments')
