#!/usr/bin/env python3
"""Verify and publish immutable Release cache artifacts from successful main CI.

Default/help does nothing. `probe` is read only. `package` requires a successful
full-build log and explicit source/exit-code evidence; it probes Releases first.
`publish` is a separate, explicit remote mutation after local verification.
Only the publisher's output directory is written; .lake/build is always read.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile

REPOSITORY = 'SII-MATH/Kervaire126Main'
WORKTREE = Path('/inspire/hdd/global_user/czxs25250150/kip126-ci/runner/_work/Kervaire126Main/Kervaire126Main')
BASE = Path(__file__).resolve().parent
TAG_RE = re.compile(r'build-cache-[0-9a-f]{40}-linux-x86_64')
HEX40 = re.compile(r'[0-9a-f]{40}')
HEX64 = re.compile(r'[0-9a-f]{64}')
MAX_ARCHIVE = 2 * 1024**3
MAX_EXPANDED = 16 * 1024**3


def run(*args, cwd=None, timeout=120):
    if args and args[0] == 'git':
        args = ('git', '-c', 'core.fsmonitor=false', '-c', 'core.hooksPath=/dev/null', *args[1:])
    return subprocess.check_output(args, cwd=cwd, stderr=subprocess.PIPE, timeout=timeout)


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            guard()
            result.update(chunk)
    return result.hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def load_ci(root):
    spec = importlib.util.spec_from_file_location('project_ci_cache', Path(__file__).with_name('ci-cache.py'))
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    return module


def api(endpoint):
    return json.loads(run('gh', 'api', endpoint))


def controlled_ci_cache(root):
    ci_home = Path('/inspire/hdd/global_user/czxs25250150/kip126-ci')
    ci_root = ci_home / 'runner/_work/Kervaire126Main/Kervaire126Main'
    digest = hashlib.sha256()
    for name in ('lean-toolchain', 'lake-manifest.json'):
        digest.update(name.encode() + b'\0' + (root / name).read_bytes() + b'\0')
    target = ci_home / 'cache/environments' / digest.hexdigest()
    try:
        return (root == ci_root and (root / '.lake').is_symlink() and
                (root / '.lake').resolve(strict=True) == target and target.resolve() == target and
                (target / 'runner-cache-layout').read_text().strip() == 'single-slot-v1' and
                (target / 'runner-environment').read_text().strip() == digest.hexdigest())
    except (OSError, ValueError):
        return False


def snapshot(root, expected_source=None):
    if (platform.system().lower(), platform.machine()) != ('linux', 'x86_64'):
        raise ValueError('This publisher is restricted to linux x86_64')
    root = root.resolve(strict=True)
    head = run('git', 'rev-parse', 'HEAD', cwd=root).decode().strip()
    if not HEX40.fullmatch(head) or expected_source is not None and expected_source != head:
        raise ValueError('The actual build source must be the full current HEAD commit')
    status_rows = run('git', 'status', '--porcelain=v1', '-z', '--untracked-files=all', cwd=root).split(b'\0')
    # The runner's runtime .lake symlink is not a source file. Permit only this
    # exact untracked entry, after validating its dedicated environment/markers.
    # Independently checking every committed input blob below remains mandatory.
    if any(row and not (row == b'?? .lake' and controlled_ci_cache(root)) for row in status_rows):
        raise ValueError('Checkout has uncommitted/untracked source files; commit first')
    remote = run('git', 'remote', 'get-url', 'origin', cwd=root).decode().strip()
    if remote not in {f'https://github.com/{REPOSITORY}.git', f'https://github.com/{REPOSITORY}', f'git@github.com:{REPOSITORY}.git'}:
        raise ValueError('Unexpected origin repository')
    ci = load_ci(root)
    inputs = ci.build_inputs(root)
    # Independently compare selected paths, modes and bytes against committed
    # blobs, rather than treating a clean index as sufficient provenance.
    selected = []
    for row in run('git', 'ls-tree', '-rz', '--full-tree', head, cwd=root).split(b'\0'):
        if not row:
            continue
        header, raw_path = row.split(b'\t', 1)
        mode, kind, oid = header.decode().split()
        path = raw_path.decode()
        if not (path.endswith('.lean') or path in {'lean-toolchain', 'lake-manifest.json'} or
                path.startswith('interface/baselines/') and path.endswith('.json') or
                path.startswith('scripts/')):
            continue
        if kind != 'blob' or mode not in {'100644', '100755'}:
            raise ValueError(f'Unsupported committed input: {path}')
        selected.append((path, mode, oid))
    # Batch object reads instead of starting one Git process per source file.
    objects = subprocess.run(['git', 'cat-file', '--batch'], cwd=root,
                             input=''.join(oid + '\n' for _, _, oid in selected).encode(),
                             check=True, capture_output=True, timeout=120).stdout
    import io
    stream = io.BytesIO(objects)
    committed = []
    for path, mode, oid in selected:
        header = stream.readline().decode().strip().split()
        if len(header) != 3 or header[:2] != [oid, 'blob']:
            raise ValueError('Committed build input object is missing')
        blob = stream.read(int(header[2]))
        if len(blob) != int(header[2]) or stream.read(1) != b'\n':
            raise ValueError('Truncated committed input object')
        committed.append({'path': path, 'mode': mode, 'sha256': digest_bytes(blob)})
    committed.sort(key=lambda item: item['path'])
    if inputs['files'] != committed:
        raise ValueError('Working build inputs differ from HEAD blobs')
    toolchain = (root / 'lean-toolchain').read_text().strip()
    # Never execute runner-writable toolchain binaries with publisher privileges.
    lean_version = run('/usr/sbin/runuser', '-u', 'kip-ci', '--',
                       str(WORKTREE.parents[3] / '.elan/bin/lean'), '--version', cwd=root).decode().strip()
    version = toolchain.rsplit(':v', 1)[-1]
    if not lean_version.startswith(f'Lean (version {version}, x86_64-unknown-linux-gnu,'):
        raise ValueError('Active Lean executable differs from the pinned toolchain/platform')
    return {'root': root, 'ci': ci, 'head': head,
            'tree': run('git', 'rev-parse', 'HEAD^{tree}', cwd=root).decode().strip(),
            'inputs': inputs, 'toolchain': toolchain, 'lean_version': lean_version,
            'manifest_sha256': digest_file(root / 'lake-manifest.json')}


def safe_name(name):
    if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', name):
        raise ValueError(f'Unsafe asset name: {name!r}')
    return name


def download(tag, name, directory, assets=None):
    safe_name(name)
    destination = directory / name
    remote = None if assets is None else assets.get(name)
    if assets is not None:
        if remote is None:
            raise ValueError(f'Release asset is missing remotely: {tag}/{name}')
        # Reusing a previously downloaded file requires a live, server-computed
        # SHA-256 and matching size. Otherwise fetch fresh bytes this round.
        reusable = (destination.is_file() and not destination.is_symlink() and
                    remote.get('digest') == f'sha256:{digest_file(destination)}' and
                    destination.stat().st_size == remote.get('size'))
        if destination.exists() and not reusable:
            if not destination.is_file() or destination.is_symlink():
                raise ValueError(f'Invalid local asset path: {destination}')
            destination.unlink()
    if not destination.exists():
        run('gh', 'release', 'download', tag, '--repo', REPOSITORY,
            '--pattern', name, '--dir', str(directory), timeout=300)
    if not destination.is_file() or destination.is_symlink():
        raise ValueError(f'Invalid downloaded asset: {name}')
    if remote is not None:
        if destination.stat().st_size != remote.get('size'):
            raise ValueError(f'Remote asset size mismatch: {name}')
        if remote.get('digest') and remote['digest'] != f'sha256:{digest_file(destination)}':
            raise ValueError(f'Remote asset SHA-256 mismatch: {name}')
    return destination


def checksum(path, expected):
    if not isinstance(expected, str) or not HEX64.fullmatch(expected) or digest_file(path) != expected:
        raise ValueError(f'SHA-256 mismatch: {path}')


def read_sums(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        value, name = line.split(maxsplit=1)
        name = safe_name(name.lstrip('*'))
        if not HEX64.fullmatch(value) or name in result:
            raise ValueError('Invalid or duplicate SHA256SUMS entry')
        result[name] = value
    return result


def member_path(name):
    path = PurePosixPath(name)
    if (path.is_absolute() or '..' in path.parts or '\\' in name or
            path.parts[:2] != ('.lake', 'build') or str(path) != name.rstrip('/')):
        raise ValueError(f'Unsafe archive path: {name}')
    return path


def verify_archive(path, inventory, archive_meta):
    if (archive_meta.get('format') != 'tar.zst' or archive_meta.get('root') != '.lake/build' or
            not 0 < archive_meta['bytes'] <= MAX_ARCHIVE or path.stat().st_size != archive_meta['bytes']):
        raise ValueError('Invalid archive format/root/size')
    checksum(path, archive_meta['sha256'])
    for item in inventory:
        member_path(item['path'])
        if (not isinstance(item['bytes'], int) or isinstance(item['bytes'], bool) or item['bytes'] < 0 or
                not isinstance(item['sha256'], str) or not HEX64.fullmatch(item['sha256'])):
            raise ValueError('Invalid inventory size/checksum')
    expected = {item['path']: item for item in inventory}
    if len(expected) != len(inventory):
        raise ValueError('Duplicate inventory path')
    process = subprocess.Popen(['zstd', '-q', '-d', '-c', str(path)], stdout=subprocess.PIPE)
    seen, files, size, count = set(), set(), 0, 0
    try:
        with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
            for member in tar:
                guard()
                normalized = str(member_path(member.name))
                if normalized in seen or not (member.isdir() or member.isfile()):
                    raise ValueError(f'Nonregular/duplicate archive member: {member.name}')
                seen.add(normalized)
                count += 1
                size += member.size
                if size > MAX_EXPANDED or count > 200000:
                    raise ValueError('Archive expansion limit exceeded')
                if member.isdir():
                    continue
                files.add(normalized)
                expected_item = expected.get(normalized)
                if expected_item is None or member.size != expected_item['bytes']:
                    raise ValueError(f'Unexpected member or size: {member.name}')
                calculated = hashlib.sha256()
                with tar.extractfile(member) as stream:
                    for chunk in iter(lambda: stream.read(1024**2), b''):
                        calculated.update(chunk)
                if calculated.hexdigest() != expected_item['sha256']:
                    raise ValueError(f'Archived file SHA-256 mismatch: {member.name}')
        process.stdout.close()
        if process.wait() != 0 or files != set(expected):
            raise ValueError('Archive decompression failed or inventory is incomplete')
    finally:
        process.stdout.close()
        if process.poll() is None:
            process.terminate()
            process.wait()
    if '.lake/build' not in seen:
        raise ValueError('Missing archive root')
    if archive_meta.get('uncompressed_files') != len(files) or archive_meta.get('uncompressed_bytes') != size:
        raise ValueError('Archive file/byte totals differ from metadata')
    return {'files': len(files), 'bytes': size, 'safe_paths': True, 'every_file_sha256': True}


def validate_bundle(directory, current, tag=None):
    metadata = json.loads((directory / 'metadata.json').read_text())
    ci = current['ci']
    if not ci.compatible(metadata, current['inputs'], REPOSITORY,
                         current['toolchain'], current['manifest_sha256']):
        raise ValueError('Cache environment, build result or full input fingerprint differs')
    expected_tag = f'build-cache-{metadata["source_commit"]}-linux-x86_64'
    if tag is not None and tag != expected_tag:
        raise ValueError('Tag differs from the actual source commit')
    sums = read_sums(directory / 'SHA256SUMS')
    # Verify every listed artifact, including metadata, log and the input manifest.
    for name, value in sums.items():
        checksum(directory / name, value)
    if sums.get('metadata.json') != digest_file(directory / 'metadata.json'):
        raise ValueError('Metadata is absent from SHA256SUMS')
    manifest = metadata['build_inputs']
    manifest_name = safe_name(manifest['manifest'])
    if sums.get(manifest_name) != manifest['manifest_sha256']:
        raise ValueError('Build-input manifest checksum is inconsistent')
    recorded = json.loads((directory / manifest_name).read_text())
    if recorded != (current['inputs']['files'] if isinstance(recorded, list) else current['inputs']):
        raise ValueError('Full selected input manifest differs from committed HEAD')
    build = metadata['build']
    if sums.get(safe_name(build['log'])) != build['log_sha256']:
        raise ValueError('Build log checksum is inconsistent')
    archive = metadata['archive']
    inventory_name = safe_name(archive['file_inventory'])
    if sums.get(inventory_name) != archive['file_inventory_sha256']:
        raise ValueError('Inventory checksum is inconsistent')
    inventory = json.loads((directory / inventory_name).read_text())
    # Historical publishers used path/bytes, path/size, or name/size.
    inventory = [{'path': item.get('path', item.get('name')),
                  'bytes': item.get('bytes', item.get('size')), 'sha256': item['sha256']}
                 for item in inventory]
    filename = safe_name(archive['filename'])
    parts = archive['parts']
    names = [safe_name(part['filename']) for part in parts]
    if not names or len(set(names)) != len(names):
        raise ValueError('Missing or duplicate archive parts')
    for part in parts:
        if sums.get(part['filename']) != part['sha256']:
            raise ValueError('Archive-part checksum is inconsistent')
        checksum(directory / part['filename'], part['sha256'])
    whole = directory / filename
    if names != [filename]:
        if not whole.exists():
            with whole.open('xb') as stream:
                for name in names:
                    with (directory / name).open('rb') as source:
                        shutil.copyfileobj(source, stream)
    verified = verify_archive(whole, inventory, archive)
    return metadata, expected_tag, verified


def releases():
    result, page = [], 1
    while True:
        rows = api(f'repos/{REPOSITORY}/releases?per_page=100&page={page}')
        if not isinstance(rows, list):
            raise ValueError('Unexpected Release listing response')
        result.extend(row for row in rows if not row.get('draft') and TAG_RE.fullmatch(row.get('tag_name', '')))
        if len(rows) < 100:
            return sorted(result, key=lambda row: row.get('published_at') or '', reverse=True)
        page += 1


def probe(current, output_dir):
    probe_dir = output_dir / 'release-probes'
    probe_dir.mkdir(parents=True, exist_ok=True)
    candidates = releases()  # A listing/network failure must prevent packaging.
    def inspect(release):
        tag = release['tag_name']
        directory = probe_dir / tag
        directory.mkdir(exist_ok=True)
        assets = {item['name']: item for item in release.get('assets', [])}
        meta_path = download(tag, 'metadata.json', directory, assets)
        metadata = json.loads(meta_path.read_text())
        matching = current['ci'].compatible(metadata, current['inputs'], REPOSITORY,
                                            current['toolchain'], current['manifest_sha256'])
        return tag, directory, metadata, matching, assets
    # Metadata only first; no large files are fetched until complete inputs match.
    with ThreadPoolExecutor(max_workers=6) as pool:
        inspected = list(pool.map(inspect, candidates))
    for tag, directory, metadata, matching, assets in inspected:
        if not matching:
            continue
        manifest = metadata['build_inputs']
        recorded = download(tag, manifest['manifest'], directory, assets)
        checksum(recorded, manifest['manifest_sha256'])
        recorded_inputs = json.loads(recorded.read_text())
        expected = current['inputs']['files'] if isinstance(recorded_inputs, list) else current['inputs']
        if recorded_inputs != expected:
            continue
        sums_path = download(tag, 'SHA256SUMS', directory, assets)
        sums = read_sums(sums_path)
        # Verify all assets named by the published checksum manifest, including
        # every part and the complete concatenated archive and file inventory.
        for name in sums:
            download(tag, name, directory, assets)
        validated, _, verified = validate_bundle(directory, current, tag)
        if remote_tag_commit(tag) != validated['source_commit']:
            raise ValueError('Reusable Release tag resolves to a different build source')
        result = {'status': 'reuse', 'release_tag': tag,
                  'release_url': f'https://github.com/{REPOSITORY}/releases/tag/{tag}',
                  'current_commit': current['head'], 'actual_build_source_commit': validated['source_commit'],
                  'fingerprint_sha256': current['inputs']['fingerprint'],
                  'metadata_unchanged': True, 'verification': verified, 'directory': str(directory)}
        write_json(output_dir / 'reuse-result.json', result)
        print(json.dumps(result, indent=2), flush=True)
        return result
    print(f'No complete matching cache among {len(inspected)} Releases.', flush=True)
    return None


def remote_tag_commit(tag, allow_absent=False):
    try:
        value = api(f'repos/{REPOSITORY}/git/ref/tags/{tag}')['object']
    except subprocess.CalledProcessError as error:
        if allow_absent and b'HTTP 404' in (error.stderr or b''):
            return None
        raise
    seen = set()
    while value.get('type') == 'tag':
        if value['sha'] in seen or len(seen) > 10:
            raise ValueError('Invalid annotated tag chain')
        seen.add(value['sha'])
        value = api(f'repos/{REPOSITORY}/git/tags/{value["sha"]}')['object']
    if value.get('type') != 'commit' or not HEX40.fullmatch(value.get('sha', '')):
        raise ValueError('Release tag does not resolve to a commit')
    return value['sha']


def draft_release(tag):
    page = 1
    found = []
    while True:
        rows = api(f'repos/{REPOSITORY}/releases?per_page=100&page={page}')
        if not isinstance(rows, list):
            raise ValueError('Unexpected Release listing response')
        found.extend(row for row in rows if row.get('draft') and row.get('tag_name') == tag)
        if len(rows) < 100:
            break
        page += 1
    if len(found) > 1:
        raise ValueError('Multiple draft Releases exist for this tag')
    return found[0] if found else None


def guard():
    callback = globals().get('CACHE_READ_GUARD')
    if callback:
        callback()


def inventory(root):
    cache = root / '.lake/build'
    controlled = controlled_ci_cache(root)
    if ((root / '.lake').is_symlink() and not controlled) or cache.is_symlink() or not cache.is_dir():
        raise ValueError('Expected real build files or the exact controlled single-slot CI environment')
    rows = []
    guard()
    for directory, dirs, files in os.walk(cache, followlinks=False):
        for name in dirs + files:
            guard()
            path = Path(directory) / name
            info = path.lstat()
            if not (stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode)):
                raise ValueError(f'Nonregular cache object: {path}')
            if stat.S_ISREG(info.st_mode):
                before = (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns, info.st_mode)
                value = digest_file(path)
                after = path.lstat()
                if before != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns, after.st_mode):
                    raise ValueError(f'Cache changed while hashing: {path}')
                rows.append({'path': path.relative_to(root).as_posix(), 'bytes': info.st_size,
                             'sha256': value, 'mode': stat.S_IMODE(info.st_mode),
                             'mtime_ns': info.st_mtime_ns})
    rows.sort(key=lambda item: item['path'])
    if not rows or len(rows) > 200000 or sum(item['bytes'] for item in rows) > MAX_EXPANDED:
        raise ValueError('Empty or oversized project cache')
    return rows


def package(args, current):
    if args.build_exit_code != 0 or not args.build_log or not args.source_commit:
        raise ValueError('Package requires explicit source commit, full successful lake build log and exit code 0')
    log = args.build_log.resolve(strict=True)
    if not log.is_file() or log.is_symlink():
        raise ValueError('Expected a regular build log')
    text = log.read_text(errors='replace')
    if not re.search(r'^Build completed successfully(?:\s|\.|$)', text, flags=re.MULTILINE):
        raise ValueError('Full lake build log contains no successful completion line')
    if probe(current, args.output):
        return
    ci, root = current['ci'], current['root']
    if ci.active_build(root):
        raise ValueError('Active Lean/Lake build; packaging is forbidden')
    guard()
    current = snapshot(root, args.source_commit)
    before = inventory(root)
    directory = args.output / f'package-{current["head"]}'
    directory.mkdir(exist_ok=False)
    shutil.copyfile(log, directory / 'lake-build.log')
    write_json(directory / 'build-inputs.json', current['inputs'])
    write_json(directory / 'cache-files.json', before)
    archive_path = directory / 'project-build.tar.zst'
    with archive_path.open('xb') as output_stream:
        process = subprocess.Popen(['zstd', '-q', '-T2', '-3', '-c'], stdin=subprocess.PIPE, stdout=output_stream)
        try:
            # Explicit addfile prevents hardlink encoding, symlink traversal and
            # unrelated .lake/packages contents from entering the archive.
            with tarfile.open(fileobj=process.stdin, mode='w|', format=tarfile.PAX_FORMAT) as tar:
                root_info = tarfile.TarInfo('.lake/build')
                root_info.type, root_info.mode = tarfile.DIRTYPE, 0o755
                tar.addfile(root_info)
                for item in before:
                    guard()
                    member = tarfile.TarInfo(item['path'])
                    member.size, member.mode = item['bytes'], item['mode']
                    member.mtime = item['mtime_ns'] // 1000000000
                    with (root / item['path']).open('rb') as stream:
                        tar.addfile(member, stream)
            process.stdin.close()
            if process.wait() != 0:
                raise ValueError('Compression failed')
        finally:
            if not process.stdin.closed:
                process.stdin.close()
            if process.poll() is None:
                process.terminate()
                process.wait()
    archive_hash = digest_file(archive_path)
    parts = []
    with archive_path.open('rb') as source:
        while block := source.read(32 * 1024**2):
            part = directory / f'{archive_path.name}.part-{len(parts):04d}'
            part.write_bytes(block)
            parts.append({'filename': part.name, 'bytes': len(block), 'sha256': digest_bytes(block)})
    archive = {'filename': archive_path.name, 'format': 'tar.zst', 'root': '.lake/build',
               'bytes': archive_path.stat().st_size, 'sha256': archive_hash,
               'parts': parts,
               'uncompressed_files': len(before), 'uncompressed_bytes': sum(item['bytes'] for item in before),
               'file_inventory': 'cache-files.json', 'file_inventory_sha256': digest_file(directory / 'cache-files.json'),
               'verified_paths_and_regular_files': True, 'verified_every_archived_file_sha256': True,
               'stable_before_and_after_archive': True}
    verified = verify_archive(archive_path, before, archive)
    if ci.active_build(root) or before != inventory(root):
        raise ValueError('Cache changed or a build started during packaging')
    after = snapshot(root, current['head'])
    if after['inputs'] != current['inputs']:
        raise ValueError('Build inputs changed during packaging')
    metadata = {'schema_version': 1, 'created_at_utc': datetime.now(timezone.utc).isoformat(),
                'repository': REPOSITORY, 'repository_url': f'https://github.com/{REPOSITORY}.git',
                'source_commit': current['head'], 'source_tree': current['tree'],
                'os': 'linux', 'arch': 'x86_64', 'lean_toolchain': current['toolchain'],
                'lean_version': current['lean_version'], 'lake_manifest_sha256': current['manifest_sha256'],
                'build_inputs': {'fingerprint_sha256': current['inputs']['fingerprint'],
                                 'manifest': 'build-inputs.json',
                                 'manifest_sha256': digest_file(directory / 'build-inputs.json'),
                                 'scope': 'Exact scripts/ci-cache.py build_inputs: all tracked .lean files, lean-toolchain, lake-manifest.json, interface/baselines/*.json and scripts/*, with committed Git modes and SHA-256 contents.',
                                 'working_tree_matches_commit': True, 'file_count': len(current['inputs']['files'])},
                'build': {'command': 'lake build', 'status': 'passed', 'exit_code': 0,
                          'log': 'lake-build.log', 'log_sha256': digest_file(directory / 'lake-build.log'),
                          'evidence': 'Successful main CI full lake build log, explicit exit code 0 and actual source commit; successful completion line verified.',
                          'dependencies_included': False,
                          'dependency_restore': 'Restore dependency/Mathlib caches separately at lake-manifest.json locked versions.'},
                'archive': archive,
                'restore': 'Verify compatibility and SHA256SUMS before safely extracting to a temporary directory; install only with no active writers and a backup, then run full lake build.'}
    write_json(directory / 'metadata.json', metadata)
    (directory / 'SHA256SUMS').write_text(''.join(f'{digest_file(path)}  {path.name}\n' for path in sorted(directory.iterdir()) if path.is_file() and path != archive_path))
    validate_bundle(directory, current)
    write_json(args.output / 'package-result.json', {'status': 'packaged', 'directory': str(directory),
               'source_commit': current['head'], 'fingerprint_sha256': current['inputs']['fingerprint'],
               'release_tag': f'build-cache-{current["head"]}-linux-x86_64', 'verification': verified})
    print(f'Validated local cache package: {directory}\nNo upload performed.', flush=True)


def publish(args, current):
    directory = args.package_dir.resolve(strict=True)
    metadata, tag, verified = validate_bundle(directory, current)
    if probe(current, args.output):
        return
    # Confirm GitHub already knows the actual build commit; never create a
    # Release whose source commit has not yet been pushed by the parent.
    commit = api(f'repos/{REPOSITORY}/commits/{metadata["source_commit"]}')
    if commit.get('sha') != metadata['source_commit']:
        raise ValueError('Actual source commit is not available remotely')
    tagged = remote_tag_commit(tag, allow_absent=True)
    if tagged is not None and tagged != metadata['source_commit']:
        raise ValueError('Existing remote tag resolves to a different source commit')
    notes = args.output / 'release-notes.md'
    notes.write_text(f'Verified project-only `.lake/build/` cache.\n\nActual build source: `{metadata["source_commit"]}`.\nFull input fingerprint: `{current["inputs"]["fingerprint"]}`.\n\nFull `lake build` passed; locked dependency/Mathlib caches are restored separately. Verify metadata and SHA256SUMS before restoration.\n')
    sums = read_sums(directory / 'SHA256SUMS')
    expected = dict(sums, SHA256SUMS=digest_file(directory / 'SHA256SUMS'))
    saved = json.loads((directory / 'draft-release.json').read_text()) if (directory / 'draft-release.json').exists() else None
    existing = api(f'repos/{REPOSITORY}/releases/{saved["id"]}') if saved else draft_release(tag)
    if existing is None and args.release_id is not None:
        raise ValueError('Requested draft Release ID is absent; no new Release will be created')
    if existing is None:
        existing = json.loads(run('gh', 'api', '--method', 'POST', f'repos/{REPOSITORY}/releases',
                                  '-f', 'tag_name=' + tag, '-f', 'target_commitish=' + metadata['source_commit'],
                                  '-f', 'name=' + tag, '-f', 'body=' + notes.read_text(),
                                  '-F', 'draft=true', '-f', 'make_latest=false'))
        write_json(directory / 'draft-release.json', {'id': existing['id'], 'tag': tag})
    if (existing is None or existing.get('draft') is not True or existing.get('tag_name') != tag or
            existing.get('target_commitish') != metadata['source_commit']):
        raise ValueError('Draft Release does not target the exact build source')
    if args.release_id is not None and existing.get('id') != args.release_id:
        raise ValueError('Refusing to resume a different draft Release ID')
    # GitHub's server SHA-256 validates the uploaded bytes. If the server does
    # not return a digest, download that asset and verify the full SHA locally.
    # An unpublished new tag need not exist, and /releases/tags does not return
    # this draft. Its immutable Release ID is the correct read/update endpoint.
    write_json(directory / 'draft-release.json', {'id': existing['id'], 'tag': tag})
    endpoint = f'repos/{REPOSITORY}/releases/{existing["id"]}'
    published = api(endpoint)
    tagged = remote_tag_commit(tag, allow_absent=True)
    if tagged is not None and tagged != metadata['source_commit']:
        raise ValueError('Existing Release tag differs from the build source; Release remains draft')
    remote_assets = {item['name']: item for item in published.get('assets', [])}
    if set(remote_assets) - set(expected):
        raise ValueError('Draft has unexpected assets; refusing to alter it')
    missing = []
    for name, value in expected.items():
        asset = remote_assets.get(name)
        if asset is not None and (asset.get('state') != 'uploaded' or
                asset.get('size') != (directory / name).stat().st_size or
                asset.get('digest') not in {None, f'sha256:{value}'}):
            # Only the exact draft's expected artifact is replaceable. Published
            # Releases and unrelated asset names are never touched on retry.
            run('gh', 'api', '--method', 'DELETE', f'repos/{REPOSITORY}/releases/assets/{asset["id"]}')
            asset = None
        if asset is None:
            missing.append(name)
    def upload(name):
        run('gh', 'release', 'upload', tag, str(directory / name), '--repo', REPOSITORY, timeout=180)
    with ThreadPoolExecutor(max_workers=3) as pool:
        list(pool.map(upload, missing))
    published = api(endpoint)
    remote_assets = {item['name']: item for item in published.get('assets', [])}
    if set(remote_assets) != set(expected):
        raise ValueError('Draft upload incomplete; retain verified parts and retry missing assets')
    with tempfile.TemporaryDirectory(prefix='verify-upload-', dir=args.output) as temporary:
        for name, value in expected.items():
            remote_asset = remote_assets.get(name)
            if remote_asset is None or remote_asset['size'] != (directory / name).stat().st_size:
                raise ValueError(f'Uploaded asset missing or wrong size; Release remains draft: {name}')
            server_digest = remote_asset.get('digest')
            if server_digest:
                if server_digest != f'sha256:{value}':
                    raise ValueError(f'Uploaded asset SHA mismatch; Release remains draft: {name}')
            else:
                destination = Path(temporary) / name
                destination.write_bytes(run('gh', 'api',
                    f'repos/{REPOSITORY}/releases/assets/{remote_asset["id"]}',
                    '-H', 'Accept: application/octet-stream', timeout=180))
                checksum(destination, value)
    run('gh', 'api', '--method', 'PATCH', endpoint, '-F', 'draft=false', '-f', 'make_latest=false')
    final = api(endpoint)
    if (final.get('draft') is not False or final.get('id') != published.get('id') or
            final.get('tag_name') != tag or remote_tag_commit(tag) != metadata['source_commit']):
        raise ValueError('Release publication was not confirmed')
    final_assets = {item['name']: item for item in final.get('assets', [])}
    if set(final_assets) != set(expected):
        raise ValueError('Published Release assets differ from the verified draft')
    for name, value in expected.items():
        item = final_assets[name]
        if (item['id'] != remote_assets[name]['id'] or item.get('state') != 'uploaded' or
                item.get('size') != (directory / name).stat().st_size or
                item.get('digest') is not None and item['digest'] != f'sha256:{value}'):
            raise ValueError(f'Published asset differs from its validated upload: {name}')
    result = {'status': 'published', 'release_tag': tag, 'actual_build_source_commit': metadata['source_commit'],
              'current_commit': current['head'], 'fingerprint_sha256': current['inputs']['fingerprint'],
              'release_url': f'https://github.com/{REPOSITORY}/releases/tag/{tag}',
              'verification': verified, 'uploaded_sha256_verified': True}
    write_json(args.output / 'publish-result.json', result)
    write_json(args.output / 'publication-verification.json', result | {
        'release_id': final['id'], 'draft': final['draft'],
        'tag_commit': metadata['source_commit'], 'archive_sha256': metadata['archive']['sha256'],
        'lean_toolchain': metadata['lean_toolchain'], 'lake_manifest_sha256': metadata['lake_manifest_sha256'],
        'assets': [{'name': name, 'bytes': final_assets[name]['size'], 'expected_sha256': value,
                    'server_digest': final_assets[name].get('digest'), 'state': final_assets[name]['state']}
                   for name, value in sorted(expected.items())]})
    print(json.dumps(result, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['inspect', 'probe', 'package', 'verify', 'publish'])
    parser.add_argument('--worktree', type=Path, default=WORKTREE)
    parser.add_argument('--output', type=Path, default=BASE / 'artifacts')
    parser.add_argument('--source-commit')
    parser.add_argument('--build-log', type=Path)
    parser.add_argument('--build-exit-code', type=int)
    parser.add_argument('--package-dir', type=Path)
    parser.add_argument('--release-id', type=int, help='Resume only this exact existing draft Release ID')
    args = parser.parse_args()
    if args.command in {'verify', 'publish'} and not args.package_dir:
        parser.error('--package-dir is required')
    if args.command == 'package' and (not args.source_commit or not args.build_log or args.build_exit_code != 0):
        parser.error('package requires --source-commit FULL_SHA --build-log PATH --build-exit-code 0')
    args.output = args.output.resolve()
    if args.worktree.resolve() == args.output or args.worktree.resolve() in args.output.parents:
        raise ValueError('Output must be outside the worktree')
    current = snapshot(args.worktree, args.source_commit)
    if args.command == 'inspect':
        print(json.dumps({key: current[key] for key in ['head', 'tree', 'toolchain', 'lean_version', 'manifest_sha256']} |
                         {'fingerprint_sha256': current['inputs']['fingerprint'], 'input_files': len(current['inputs']['files'])}, indent=2))
        return
    args.output.mkdir(parents=True, exist_ok=True)
    if args.command == 'probe':
        probe(current, args.output)
    elif args.command == 'package':
        package(args, current)
    elif args.command == 'verify':
        metadata, tag, verified = validate_bundle(args.package_dir, current)
        print(json.dumps({'tag': tag, 'actual_build_source_commit': metadata['source_commit'], 'verification': verified}, indent=2))
    else:
        publish(args, current)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr.decode(errors='replace'), file=sys.stderr)
        sys.exit(1)
