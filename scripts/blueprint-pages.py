#!/usr/bin/env python3
"""Publish current-source Pages from a fixed, verified public evidence seed.

The seed contains project declaration evidence, not hgraph implementation code.
Publication first tries independent mathematical-source verification; a failed
whole-repository audit is never a prerequisite for publishing honest mappings.
"""
import argparse
from copy import deepcopy
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import tempfile
from urllib.parse import urlparse
from urllib.request import HTTPRedirectHandler, build_opener

ROOT = Path(__file__).resolve().parents[1]
SEED_FILES = frozenset(('verified-source-snapshot.json',
                        'verified-source-snapshot.sha256',
                        'paper-binding-baseline/validation.json'))
MAX_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_MEMBER_BYTES = 128 * 1024 * 1024
MAX_TOTAL_BYTES = 256 * 1024 * 1024
REQUIRED_CHECKS = frozenset(('lake_build', 'source_to_kernel_unique',
    'all_locked_public_interfaces_visible', 'all_direct_holes_registered_and_visible',
    'native_closure_matches_kernel_for_every_source_declaration',
    'unchanged_inputs_during_capture', 'pinned_native_code_and_frontend_verified'))


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(',', ':')) + '\n').encode()


def fingerprint(value):
    # Match build-blueprint.py's existing mathematical-input fingerprint.
    return sha256(json.dumps(value, sort_keys=True).encode())


def checked_evidence(evidence):
    if not isinstance(evidence, dict):
        raise ValueError('Invalid seed evidence')
    checks = evidence.get('checks', {})
    if (not isinstance(checks, dict) or not REQUIRED_CHECKS <= checks.keys()
            or any(value is not True for value in checks.values())):
        raise ValueError('Seed requires complete, successful compiled verification checks')
    inputs = evidence.get('inputs')
    if not isinstance(inputs, dict) or not inputs or fingerprint(inputs) != evidence.get('input_fingerprint'):
        raise ValueError('Seed mathematical-input fingerprint mismatch')
    for name, digest in inputs.items():
        if (not isinstance(name, str) or PurePosixPath(name).is_absolute()
                or '..' in PurePosixPath(name).parts or not isinstance(digest, str)
                or not re.fullmatch('[0-9a-f]{64}', digest)):
            raise ValueError('Invalid seed mathematical input')
    if not re.fullmatch('[0-9a-f]{40}', evidence.get('source_commit', '')):
        raise ValueError('Seed source commit is missing')
    build = evidence.get('full_project_build', {})
    if (build.get('status') != 'passed'
            or build.get('input_fingerprint') != evidence['input_fingerprint']
            or not re.fullmatch('[0-9a-f]{64}', build.get('log_sha256', ''))):
        raise ValueError('Seed full-build evidence is missing or inconsistent')


def validate_seed(files):
    if set(files) != SEED_FILES:
        raise ValueError('Seed must contain exactly the three expected evidence files')
    snapshot_bytes = files['verified-source-snapshot.json']
    if files['verified-source-snapshot.sha256'].decode('ascii') != sha256(snapshot_bytes):
        raise ValueError('Verified source snapshot checksum mismatch')
    snapshot = json.loads(snapshot_bytes)
    if not isinstance(snapshot, dict) or set(snapshot) != {'sources', 'dependencies', 'evidence'}:
        raise ValueError('Invalid source snapshot keys')
    evidence = snapshot['evidence']
    checked_evidence(evidence)
    if json.loads(files['paper-binding-baseline/validation.json']) != evidence:
        raise ValueError('Baseline and source-snapshot evidence differ')
    sources, dependencies = snapshot['sources'], snapshot['dependencies']
    if (not isinstance(sources, dict) or not sources or not isinstance(dependencies, dict)
            or set(dependencies) != set(sources)):
        raise ValueError('Invalid source dependency index')
    for name, source in sources.items():
        if (not isinstance(source, dict) or source.get('row', {}).get('name') != name
                or source.get('file') not in evidence['inputs']
                or not isinstance(dependencies[name], list)
                or len(set(dependencies[name])) != len(dependencies[name])
                or not set(dependencies[name]) <= sources.keys()):
            raise ValueError('Invalid compiled source record or dependency')
    if len(sources) != evidence.get('source_declarations'):
        raise ValueError('Seed source-declaration count mismatch')
    return snapshot


def builder():
    sys.path.insert(0, str(ROOT / 'scripts'))
    spec = importlib.util.spec_from_file_location('pages_blueprint_builder', ROOT / 'scripts/build-blueprint.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def pack_seed(output):
    b = builder()
    b.verify_native_runtime()
    before = b.inputs()
    capture = b.STATE / 'kernel.json'
    checkpoint = json.loads((b.STATE / 'capture-inputs.json').read_text())
    validation_path = b.STATE / 'validation.json'
    evidence = deepcopy(json.loads(validation_path.read_text()))
    if (checkpoint.get('inputs') != before or evidence.get('inputs') != before
            or checkpoint.get('capture_sha256') != sha256(capture.read_bytes())):
        raise ValueError('Current inputs, compiled capture and full verification must match')
    log = b.STATE / 'build.log'
    log_text = log.read_text()
    if ('Build completed successfully' not in log_text or 'error: build failed' in log_text
            or log.stat().st_mtime_ns > validation_path.stat().st_mtime_ns):
        raise ValueError('A successful full-build log preceding this validation is required')
    evidence['full_project_build'] = {'status': 'passed',
        'log_sha256': sha256(log.read_bytes()),
        'input_fingerprint': b.fingerprint(before),
        'scope': 'Complete build for the seed inputs; current publication is verified separately.'}
    checked_evidence(evidence)
    rows = json.loads(capture.read_text())
    sources = b.index_sources(rows)
    b.validate_api_coverage(sources)
    dependencies = b.project_dependencies(rows, sources)
    obligations = {row['name']: row for row in json.loads(
        (ROOT / 'metadata/proof-obligations.json').read_text())['obligations']}
    b.validate_kernel(rows, sources, dependencies, obligations)
    snapshot = json_bytes({'sources': sources,
        'dependencies': {name: sorted(deps) for name, deps in dependencies.items()},
        'evidence': evidence})
    files = {'verified-source-snapshot.json': snapshot,
             'verified-source-snapshot.sha256': sha256(snapshot).encode('ascii'),
             'paper-binding-baseline/validation.json': json_bytes(evidence)}
    validate_seed(files)
    if b.inputs() != before:
        raise ValueError('Mathematical inputs changed while packing seed')
    output.parent.mkdir(parents=True, exist_ok=True)
    # Fixed order, metadata and gzip timestamp make identical evidence reproducible.
    with output.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(mode='w|', fileobj=compressed, format=tarfile.USTAR_FORMAT) as archive:
                for name in sorted(files):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode, info.mtime = len(files[name]), 0o644, 0
                    archive.addfile(info, io.BytesIO(files[name]))
    print(json.dumps({'seed': str(output), 'sha256': sha256(output.read_bytes()),
                      'bytes': output.stat().st_size, 'source_commit': evidence['source_commit']}))


class HTTPSRedirects(HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, message, headers, newurl):
        if urlparse(newurl).scheme != 'https':
            raise ValueError('Seed download redirected outside HTTPS')
        return super().redirect_request(request, fp, code, message, headers, newurl)


def download_seed(url, destination):
    parsed = urlparse(url)
    if (parsed.scheme != 'https' or parsed.hostname != 'github.com'
            or parsed.username or parsed.password or parsed.query or parsed.fragment
            or not re.fullmatch(r'/SII-MATH/Kervaire126Main/releases/download/[^/]+/[^/]+', parsed.path)):
        raise ValueError('Seed URL must name a fixed HTTPS GitHub Release asset in this repository')
    with build_opener(HTTPSRedirects()).open(url, timeout=60) as response, destination.open('wb') as output:
        total = 0
        while chunk := response.read(1024 * 1024):
            total += len(chunk)
            if total > MAX_ARCHIVE_BYTES:
                raise ValueError('Seed archive exceeds download limit')
            output.write(chunk)


def read_seed(path, expected_sha256):
    if not re.fullmatch('[0-9a-f]{64}', expected_sha256):
        raise ValueError('Expected seed SHA-256 must contain 64 lowercase hexadecimal digits')
    if path.stat().st_size > MAX_ARCHIVE_BYTES or sha256(path.read_bytes()) != expected_sha256:
        raise ValueError('Seed archive checksum or size mismatch')
    files, total = {}, 0
    # Never call extract/extractall: validate all metadata before installing bytes.
    class SeedMember(tarfile.TarInfo):
        def _proc_member(self, archive):
            # Check extension headers too, before tarfile consumes their payloads.
            if (self.name not in SEED_FILES or not self.isfile()
                    or self.size < 0 or self.size > MAX_MEMBER_BYTES):
                raise ValueError('Unexpected or unsafe seed archive member')
            return super()._proc_member(archive)

    with tarfile.open(path, mode='r|gz', tarinfo=SeedMember) as archive:
        for member in archive:
            if (member.name not in SEED_FILES or member.name in files
                    or not member.isfile() or member.pax_headers
                    or member.size < 0 or member.size > MAX_MEMBER_BYTES):
                raise ValueError('Unexpected, duplicate or unsafe seed archive member')
            total += member.size
            if total > MAX_TOTAL_BYTES:
                raise ValueError('Seed archive exceeds expanded-size limit')
            files[member.name] = archive.extractfile(member).read()
    validate_seed(files)
    return files


def install_seed(files):
    state = ROOT / '.lake/blueprint'
    for name in sorted(files):
        destination = state / name
        for path in (destination, *destination.parents):
            if path == ROOT:
                break
            if path.is_symlink():
                raise ValueError('Refusing a symlink in the seed installation path')
        destination.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as output:
            output.write(files[name])
            temporary = Path(output.name)
        temporary.replace(destination)


def source_branch():
    return (os.environ.get('GITHUB_REF_NAME') or subprocess.check_output(
        ['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() or None)


def publish(seed_url, seed_sha256):
    with tempfile.TemporaryDirectory(prefix='blueprint-pages-') as directory:
        archive = Path(directory) / 'seed.tar.gz'
        download_seed(seed_url, archive)
        files = read_seed(archive, seed_sha256)
    install_seed(files)
    command = [sys.executable, 'scripts/publish-blueprint.py']
    refreshed = subprocess.run(command + ['--refresh-source-evidence'], cwd=ROOT)
    if refreshed.returncode:
        print('Mathematical-source refresh failed; publishing mappings with explicit unverified states.', flush=True)
        install_seed(files)
        subprocess.run(command, cwd=ROOT, check=True)
    site = ROOT / '_site'
    validation_bytes = (site / 'validation.json').read_bytes()
    evidence = json.loads(validation_bytes)
    if not evidence.get('checks') or any(value is not True for value in evidence['checks'].values()):
        raise ValueError('Publication verification checks failed')
    for name, digest in evidence['site_inputs'].items():
        if sha256((ROOT / name).read_bytes()) != digest:
            raise ValueError('Site inputs changed after publication')
    original = json.loads(files['paper-binding-baseline/validation.json'])
    if evidence['source_commit'] != original['source_commit']:
        raise ValueError('Publication rewrote the baseline source commit')
    repository = os.environ.get('GITHUB_REPOSITORY', 'SII-MATH/Kervaire126Main')
    run_id = os.environ.get('GITHUB_RUN_ID')
    receipt = {'schema_version': 2, 'repository': repository,
        'source_branch': source_branch(),
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'workflow_run_url': f'https://github.com/{repository}/actions/runs/{run_id}' if run_id else None,
        'seed_url': seed_url, 'seed_sha256': seed_sha256,
        'baseline_source_commit': original['source_commit'],
        'validation_sha256': sha256(validation_bytes),
        'site_inputs': evidence['site_inputs'],
        'site_input_fingerprint': evidence['site_input_fingerprint'],
        'refreshed_all_mathematical_source_evidence': evidence.get('refreshed_all_mathematical_source_evidence', False),
        'unverified_source_labels': evidence.get('unverified_source_labels', []),
        'scope': 'Current-source publication; baseline commit and whole-repository verification remain separate.'}
    (site / 'pages-deployment.json').write_bytes(json_bytes(receipt))
    (site / '.nojekyll').touch()
    print(f'Published current-source Pages for {receipt["source_commit"]}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    pack = commands.add_parser('pack-seed')
    pack.add_argument('--output', required=True, type=Path)
    release = commands.add_parser('publish')
    release.add_argument('--seed-url', required=True)
    release.add_argument('--seed-sha256', required=True)
    args = parser.parse_args()
    if args.command == 'pack-seed':
        pack_seed(args.output)
    else:
        publish(args.seed_url, args.seed_sha256)


if __name__ == '__main__':
    main()
