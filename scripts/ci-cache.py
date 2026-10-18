#!/usr/bin/env python3
"""Conservative CI event selection and verified, exact-input Release cache reuse.

A cache is an optimization only: every selected event still runs full `lake build`.
This script never installs a cache whose mathematical/build inputs differ.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
from urllib.parse import urlencode


ROOT = Path(__file__).resolve().parents[1]
MAX_ARCHIVE = 2 * 1024**3
MAX_EXPANDED = 16 * 1024**3


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def run(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, stderr=subprocess.PIPE, timeout=30)


def api(endpoint):
    return json.loads(run('gh', 'api', endpoint))


def output(name, value):
    print(f'{name}={value}')
    if path := os.environ.get('GITHUB_OUTPUT'):
        with open(path, 'a') as stream:
            stream.write(f'{name}={value}\n')


def needs_build(event, ref, repository, commit, pulls):
    """Only redundant develop pushes are omitted; PR/main/manual always build."""
    if event != 'push' or ref != 'refs/heads/develop':
        return True
    for pr in pulls:
        if not isinstance(pr, dict):
            continue
        head, base = pr.get('head') or {}, pr.get('base') or {}
        if (pr.get('state') == 'open' and
                head.get('ref') == 'develop' and head.get('sha') == commit and
                (head.get('repo') or {}).get('full_name') == repository and
                (base.get('repo') or {}).get('full_name') == repository and base.get('ref') == 'main'):
            return False
    return True


def plan():
    event, ref = os.environ.get('GITHUB_EVENT_NAME'), os.environ.get('GITHUB_REF')
    repository, commit = os.environ['GITHUB_REPOSITORY'], os.environ['GITHUB_SHA']
    pulls = []
    if event == 'push' and ref == 'refs/heads/develop':
        query = urlencode({'state': 'open', 'base': 'main',
                           'head': repository.split('/')[0] + ':develop', 'per_page': 100})
        try:
            pulls = api(f'repos/{repository}/pulls?{query}')
            if not isinstance(pulls, list):
                raise ValueError('unexpected pull-request response')
        except (subprocess.SubprocessError, ValueError) as error:
            print(f'PR lookup unavailable; retaining the develop build: {error}')
    build = needs_build(event, ref, repository, commit, pulls)
    output('build', str(build).lower())
    if not build:
        print('The exact develop commit has an open PR to main; its required Lean checks run there.')


def build_inputs(root=ROOT):
    """Use the existing Release manifest schema, including file modes and contents."""
    files = []
    for entry in run('git', 'ls-files', '--stage', '-z', cwd=root).split(b'\0'):
        if not entry:
            continue
        info, raw_path = entry.split(b'\t', 1)
        mode, _, stage = info.decode().split()
        path = raw_path.decode()
        if not (path.endswith('.lean') or path in {'lean-toolchain', 'lake-manifest.json'} or
                (path.startswith('metadata/') and path.endswith('.json')) or path.startswith('scripts/')):
            continue
        if stage != '0' or mode not in {'100644', '100755'}:
            raise ValueError(f'Unsupported build input: {path}')
        full = root / path
        if full.is_symlink():
            raise ValueError(f'Symlink build input: {path}')
        files.append({'path': path, 'mode': mode, 'sha256': sha256(full.read_bytes())})
    files.sort(key=lambda row: row['path'])
    fingerprint = sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode())
    return {'algorithm': 'sha256', 'fingerprint': fingerprint, 'files': files}


def compatible(metadata, inputs, repository, toolchain, manifest_hash):
    return (metadata.get('schema_version') == 1 and metadata.get('repository') == repository and
            metadata.get('os') == platform.system().lower() and metadata.get('arch') == platform.machine() and
            metadata.get('lean_toolchain') == toolchain and metadata.get('lake_manifest_sha256') == manifest_hash and
            metadata.get('build', {}).get('status') == 'passed' and
            metadata.get('build', {}).get('command') == 'lake build' and
            metadata.get('build_inputs', {}).get('working_tree_matches_commit') is True and
            metadata.get('build_inputs', {}).get('fingerprint_sha256') == inputs['fingerprint'] and
            re.fullmatch(r'[0-9a-f]{40}', metadata.get('source_commit', '')) is not None)


def safe_filename(name):
    if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', name):
        raise ValueError(f'Unsafe asset filename: {name!r}')
    return name


def download(repository, tag, filename, directory):
    safe_filename(filename)
    subprocess.run(['gh', 'release', 'download', tag, '--repo', repository,
                    '--pattern', filename, '--dir', str(directory)], cwd=ROOT,
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                   timeout=120 if '.tar.zst' in filename else 20)
    return directory / filename


def verify_file(path, expected):
    if not isinstance(expected, str) or not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('Missing/invalid SHA-256')
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            digest.update(chunk)
    if digest.hexdigest() != expected:
        raise ValueError(f'SHA-256 mismatch: {path.name}')


def extract_archive(archive, destination):
    """Streaming extraction: project build only, no links, duplicate paths or devices."""
    process = subprocess.Popen(['zstd', '-q', '-d', '-c', str(archive)], stdout=subprocess.PIPE)
    total = count = 0
    seen = set()
    try:
        with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
            for member in tar:
                path = PurePosixPath(member.name)
                if (path.is_absolute() or '..' in path.parts or '\\' in member.name or
                        path.parts[:2] != ('.lake', 'build') or
                        not (member.isdir() or member.isfile()) or path in seen):
                    raise ValueError(f'Unsafe archive member: {member.name}')
                seen.add(path)
                total += member.size
                count += 1
                if total > MAX_EXPANDED or count > 200000:
                    raise ValueError('Archive expansion limit exceeded')
                target = destination.joinpath(*path.parts)
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with tar.extractfile(member) as source, target.open('xb') as output_stream:
                        shutil.copyfileobj(source, output_stream)
                    target.chmod(member.mode & 0o777)
                    os.utime(target, (member.mtime, member.mtime))
        process.stdout.close()
        if process.wait() != 0:
            raise ValueError('zstd decompression failed')
        if not (destination / '.lake/build').is_dir():
            raise ValueError('Archive contains no project build')
    except BaseException:
        process.stdout.close()
        if process.poll() is None:
            process.terminate()
        process.wait()
        raise


def active_build(root):
    """Do not replace a cache being written by another Lean/Lake process."""
    for proc in Path('/proc').glob('[0-9]*'):
        try:
            if (proc / 'comm').read_text().strip() not in {
                    'lean', 'lake', 'leanc', 'clang', 'clang++', 'cc', 'gcc', 'c++', 'g++'}:
                continue
            cwd = (proc / 'cwd').resolve()
            if cwd == root or root in cwd.parents:
                return True
        except (OSError, RuntimeError):
            continue
    return False


def install_build(staged, root, backup):
    if active_build(root):
        raise ValueError('Active Lean/Lake build; refusing to replace project cache')
    target = root / '.lake/build'
    if target.is_symlink() or (root / '.lake').is_symlink():
        raise ValueError('Refusing symlink cache destinations')
    target.parent.mkdir(parents=True, exist_ok=True)
    moved = False
    if target.exists():
        target.rename(backup)
        moved = True
    try:
        staged.rename(target)
    except BaseException:
        if moved:
            backup.rename(target)
        raise


def restore_release():
    repository = os.environ['GITHUB_REPOSITORY']
    # Replacement is restricted to this CI checkout before compilation starts.
    if os.environ.get('GITHUB_ACTIONS') != 'true' or Path(os.environ['GITHUB_WORKSPACE']).resolve() != ROOT:
        raise ValueError('Release restoration is restricted to the fresh CI workspace')
    inputs = build_inputs()
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    manifest_hash = sha256((ROOT / 'lake-manifest.json').read_bytes())
    releases = api(f'repos/{repository}/releases?per_page=30')
    prefix = 'build-cache-'
    suffix = f'-{platform.system().lower()}-{platform.machine()}'
    candidates = [release for release in releases if not release.get('draft') and
                  release.get('tag_name', '').startswith(prefix) and
                  release.get('tag_name', '').endswith(suffix)]
    current_tag = f'{prefix}{os.environ.get("GITHUB_SHA", "")}{suffix}'
    candidates.sort(key=lambda release: release['tag_name'] != current_tag)
    # Small manifests first; never download a large archive for an incompatible snapshot.
    # Keep a cache miss cheap; old snapshots remain an optional incremental baseline.
    for release in candidates[:8]:
        tag = release['tag_name']
        with tempfile.TemporaryDirectory(prefix='ci-release-', dir=ROOT / '.lake') as temporary:
            directory = Path(temporary)
            try:
                meta_path = download(repository, tag, 'metadata.json', directory)
                metadata = json.loads(meta_path.read_text())
                if not compatible(metadata, inputs, repository, toolchain, manifest_hash):
                    continue
                if tag != f'{prefix}{metadata["source_commit"]}{suffix}':
                    raise ValueError('Release tag/source commit mismatch')
                manifest = metadata['build_inputs']
                recorded = download(repository, tag, manifest['manifest'], directory)
                verify_file(recorded, manifest['manifest_sha256'])
                if json.loads(recorded.read_text()) != inputs:
                    raise ValueError('Release input manifest differs from the checkout')
                archive_meta = metadata['archive']
                if (archive_meta['root'] != '.lake/build' or archive_meta['format'] != 'tar.zst' or
                        not 0 < archive_meta['bytes'] <= MAX_ARCHIVE):
                    raise ValueError('Invalid archive metadata')
                filename = safe_filename(archive_meta['filename'])
                parts = archive_meta['parts']
                names = [safe_filename(part['filename']) for part in parts]
                if not names or len(set(names)) != len(names):
                    raise ValueError('Missing/duplicate archive parts')
                sums = download(repository, tag, 'SHA256SUMS', directory).read_text()
                checksums = dict((name.lstrip('*'), digest) for digest, name in
                                 (line.split(maxsplit=1) for line in sums.splitlines() if line.strip()))
                if checksums.get('metadata.json') != sha256(meta_path.read_bytes()):
                    raise ValueError('Metadata checksum mismatch')
                if checksums.get(manifest['manifest']) != manifest['manifest_sha256']:
                    raise ValueError('Input manifest checksum mismatch')
                for part in parts:
                    name = part['filename']
                    if checksums.get(name) != part['sha256']:
                        raise ValueError('Part checksum metadata mismatch')
                    path = download(repository, tag, name, directory)
                    verify_file(path, part['sha256'])
                archive = directory / filename
                if names != [filename]:
                    with archive.open('xb') as destination:
                        for name in names:
                            with (directory / name).open('rb') as source:
                                shutil.copyfileobj(source, destination)
                if archive.stat().st_size != archive_meta['bytes']:
                    raise ValueError('Archive size mismatch')
                verify_file(archive, archive_meta['sha256'])
                staged = directory / 'staged'
                extract_archive(archive, staged)
                # The restored Actions cache is only a baseline; no build has run yet.
                # Keep it in place until every validation succeeds, then back it up.
                install_build(staged / '.lake/build', ROOT, directory / 'previous-build')
                print(f'Restored exact-input Release cache: {tag}; full lake build still required')
                return
            except (KeyError, OSError, ValueError, subprocess.SubprocessError, tarfile.TarError) as error:
                print(f'Ignoring unusable Release cache {tag}: {error}')
    print('No matching Release cache; using Actions cache or an incremental build')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['plan', 'inputs', 'restore-release'])
    command = parser.parse_args().command
    if command == 'plan':
        plan()
    elif command == 'inputs':
        print(json.dumps(build_inputs(), indent=2))
    else:
        (ROOT / '.lake').mkdir(exist_ok=True)
        restore_release()


if __name__ == '__main__':
    main()
