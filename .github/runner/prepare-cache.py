#!/usr/bin/env python3
"""Reuse one CI-owned incremental cache per pinned toolchain and dependency lock."""
import hashlib
import os
from pathlib import Path
import time

LAYOUT = 'single-slot-v1'


def environment_key(root):
    digest = hashlib.sha256()
    for name in ('lean-toolchain', 'lake-manifest.json'):
        digest.update(name.encode() + b'\0' + (root / name).read_bytes() + b'\0')
    return digest.hexdigest()


def valid_hash(value):
    return len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def prepare(root, cache):
    lake = root / '.lake'
    expected = environment_key(root)
    cache = cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    target = cache / expected
    if target.resolve() != target:
        raise ValueError('Persistent CI environment must be an independent directory')
    target.mkdir(exist_ok=True)
    if lake.is_symlink():
        actual = lake.resolve()
        relative = actual.relative_to(cache) if actual.is_relative_to(cache) else Path('invalid')
        parts = relative.parts
        valid = ((len(parts) == 1 and valid_hash(parts[0])) or
                 (len(parts) == 3 and valid_hash(parts[0]) and parts[1] == 'inputs' and valid_hash(parts[2])))
        if not valid:
            raise ValueError('CI .lake cannot point outside its dedicated environment cache')
        if len(parts) == 3 and parts[0] == expected and actual != target:
            # One-time migration from input snapshots: rename the active build,
            # preserving its inode and all partial progress. Never copy it.
            for name in ('build', 'config', 'lakefile.olean', 'lakefile.olean.trace'):
                source, destination = actual / name, target / name
                if source.is_symlink():
                    raise ValueError('Migrated project artifacts must be independent')
                if source.exists():
                    if destination.exists():
                        destination.rename(target / (name + '.before-single-slot-' + str(time.time_ns())))
                    source.rename(destination)
            print('Migrated active CI cache by same-filesystem rename; no build copy')
        if actual != target:
            lake.unlink()
    elif lake.exists():
        marker = lake / 'runner-environment'
        if marker.is_file() and marker.read_text().strip() == expected:
            for name in ('build', 'packages', 'config', 'lakefile.olean', 'lakefile.olean.trace'):
                source, destination = lake / name, target / name
                if source.is_symlink():
                    raise ValueError('Initial CI cache must not link to development artifacts')
                if source.exists() and not destination.exists():
                    source.rename(destination)
        # Preserve any other initial files rather than deleting them.
        lake.rename(cache / ('previous-checkout-' + str(time.time_ns())))
    for name in ('build', 'packages'):
        if (target / name).is_symlink():
            raise ValueError('CI build and dependencies must remain independent of development')
    (target / 'packages').mkdir(exist_ok=True)
    (target / 'runner-environment').write_text(expected + '\n')
    (target / 'runner-cache-layout').write_text(LAYOUT + '\n')
    if not lake.is_symlink():
        lake.symlink_to(target, target_is_directory=True)
    restore = not (target / 'build').exists()
    if output := os.environ.get('GITHUB_OUTPUT'):
        with open(output, 'a') as stream:
            stream.write('restore_release=' + str(restore).lower() + '\n')
    print('Persistent single-slot CI cache:', target)
    print('Existing build retained for Lake incremental checks:', not restore)
    print('Release bootstrap needed:', restore)
    return target


if __name__ == '__main__':
    prepare(Path(os.environ['GITHUB_WORKSPACE']), Path.home() / 'cache/environments')
