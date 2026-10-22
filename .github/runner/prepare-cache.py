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
    marker = lake / 'runner-environment'
    expected = environment_key(root)
    if lake.is_symlink():
        raise ValueError('CI .lake must be an independent directory')
    if lake.exists() and (not marker.exists() or marker.read_text().strip() != expected):
        # Never delete a previous build; it may still be useful after switching back.
        import time
        cache.mkdir(parents=True, exist_ok=True)
        old = marker.read_text().strip() if marker.exists() else 'unclassified'
        if len(old) != 64 or any(c not in '0123456789abcdef' for c in old):
            old = 'unclassified'
        lake.rename(cache / (old + '-' + str(time.time_ns())))
    lake.mkdir(exist_ok=True)
    marker.write_text(expected + '\n')
    print('Persistent CI cache environment:', expected)


if __name__ == '__main__':
    prepare(Path(os.environ['GITHUB_WORKSPACE']), Path.home() / 'cache/environments')
