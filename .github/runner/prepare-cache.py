#!/usr/bin/env python3
"""Keep local incremental caches separate for each locked Lean environment."""
import hashlib
import os
from pathlib import Path
import importlib.util
import subprocess
import tempfile


def valid_hash(value):
    return len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def seed_baseline(root, cache):
    """Called after exact Release lookup, never before it."""
    environment = cache.resolve() / environment_key(root)
    target = (root / '.lake').resolve()
    fingerprint = (target / 'runner-build-inputs').read_text().strip()
    if (not valid_hash(fingerprint) or target != environment / 'inputs' / fingerprint or
            target.resolve() != target):
        raise ValueError('Incremental target must be the current isolated input cache')
    pending = target / 'runner-incremental-baseline'
    if (target / 'build').exists():
        if (target / 'build').is_symlink():
            raise ValueError('Project build must be an independent directory')
        pending.unlink(missing_ok=True)
        print('Exact Release/current input build present; incremental copy skipped')
        return
    if not pending.exists():
        print('No incremental baseline available; retaining normal full build')
        return
    relative = Path(pending.read_text().strip())
    parts = relative.parts
    if not (parts == ('build',) or
            (len(parts) == 3 and parts[0] == 'inputs' and valid_hash(parts[1]) and parts[2] == 'build')):
        raise ValueError('Invalid incremental baseline location')
    baseline = environment / relative
    if baseline.resolve() != baseline or baseline == target / 'build':
        raise ValueError('Incremental baseline cannot escape its locked environment')
    if not baseline.is_dir():
        print('Previous baseline unavailable; retaining normal full build')
        return
    # A cancelled copy must not leave a populated-looking partial build.
    with tempfile.TemporaryDirectory(prefix='.incremental-', dir=target) as temporary:
        staged = Path(temporary) / 'build'
        subprocess.run(['cp', '-a', '--reflink=auto', str(baseline), str(staged)], check=True)
        staged.rename(target / 'build')
    pending.unlink()
    print('Exact Release unavailable; installed independent incremental baseline:', baseline)


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
    baseline = None
    if fingerprint is not None and (len(fingerprint) != 64 or any(c not in '0123456789abcdef' for c in fingerprint)):
        raise ValueError('Invalid build input fingerprint')
    if target.resolve() != target:
        raise ValueError('Persistent cache environment must be an independent directory')
    target.parent.mkdir(parents=True, exist_ok=True)
    if lake.is_symlink():
        actual = lake.resolve()
        relative = actual.relative_to(cache) if actual.is_relative_to(cache) else Path('invalid')
        parts = relative.parts
        valid = (len(parts) == 1 or (len(parts) == 3 and parts[1] == 'inputs'))
        hashes = parts if len(parts) == 1 else (parts[0], parts[-1])
        if not valid or any(len(p) != 64 or any(c not in '0123456789abcdef' for c in p) for p in hashes):
            raise ValueError('CI .lake cannot point outside the dedicated environment cache')
        if parts[0] == expected and actual != target and (actual / 'build').is_dir():
            baseline = actual / 'build'
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
    restore = not (target / 'build').exists()
    if restore and fingerprint is not None and baseline is not None:
        if baseline.is_symlink():
            raise ValueError('Incremental baseline must be an independent build directory')
        # A new source can still incrementally reuse prior artifacts. Copy-on-
        # write cloning retains both source caches; no shared writable outputs.
        (target / 'runner-incremental-baseline').write_text(str(baseline.relative_to(environment)) + '\n')
        print('Deferred incremental baseline until exact Release lookup:', baseline)
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
    if output := os.environ.get('GITHUB_OUTPUT'):
        with open(output, 'a') as stream:
            stream.write('restore_release=' + str(restore).lower() + '\n')
    print('Project cache inputs:', fingerprint or 'legacy environment')
    print('Exact project cache needs Release restore:', restore)
    return target


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed-baseline', action='store_true')
    args = parser.parse_args()
    root = Path(os.environ['GITHUB_WORKSPACE'])
    cache = Path.home() / 'cache/environments'
    if args.seed_baseline:
        seed_baseline(root, cache)
    else:
        prepare(root, cache, build_fingerprint(root))
