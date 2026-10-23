#!/usr/bin/env python3
"""Hand an exported site to the local publisher and wait for its live receipt."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
import time

SPOOL = Path('/var/lib/kip126-blueprint-publish')
REPOSITORY = 'SII-MATH/Kervaire126Main'


def context(env):
    if (env.get('GITHUB_REPOSITORY') != REPOSITORY or
            env.get('GITHUB_REF') != 'refs/heads/main' or
            env.get('GITHUB_WORKFLOW_REF') != REPOSITORY + '/.github/workflows/pages.yml@refs/heads/main' or
            env.get('GITHUB_EVENT_NAME') not in {'push', 'workflow_dispatch'} or
            not re.fullmatch('[0-9a-f]{40}', env.get('GITHUB_SHA', ''))):
        raise ValueError('Only main Blueprint exports may request publication')
    rid, attempt = env.get('GITHUB_RUN_ID', ''), env.get('GITHUB_RUN_ATTEMPT', '')
    if not re.fullmatch('[1-9][0-9]{0,19}', rid) or not re.fullmatch('[1-9][0-9]{0,5}', attempt):
        raise ValueError('Invalid Actions run identity')
    return {'repository': REPOSITORY, 'head_sha': env['GITHUB_SHA'],
            'id': int(rid), 'run_attempt': int(attempt)}


def stage(site, info, spool=SPOOL):
    for name in ('index.html', 'Kervaire126/data.json', '.hgraph-runtime/config.yaml'):
        if not (site / name).is_file():
            raise ValueError(f'Missing exported file: {name}')
    key = f"{info['id']}-{info['run_attempt']}"
    incoming = spool / 'incoming'
    with tempfile.NamedTemporaryFile(prefix='.archive-', dir=incoming) as stream:
        def regular(member):
            if not (member.isfile() or member.isdir()):
                raise ValueError(f'Unsupported website entry: {member.name}')
            return member
        with tarfile.open(fileobj=stream, mode='w') as archive:
            archive.add(site, arcname='.', filter=regular)
        stream.flush()
        os.fsync(stream.fileno())
        stream.seek(0)
        digest = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024**2), b''):
            digest.update(chunk)
        request = {**info, 'sha256': digest.hexdigest(), 'bytes': os.fstat(stream.fileno()).st_size}
        # Publish the request last; the host never sees a partially written archive.
        destination = incoming / f'{key}.tar'
        with open(destination.with_suffix('.tmp'), 'wb') as output:
            stream.seek(0)
            import shutil
            shutil.copyfileobj(stream, output)
            output.flush()
            os.fsync(output.fileno())
        destination.with_suffix('.tmp').replace(destination)
    with tempfile.NamedTemporaryFile(mode='w', prefix='.request-', dir=incoming, delete=False) as stream:
        json.dump(request, stream)
        stream.flush()
        os.fsync(stream.fileno())
    Path(stream.name).replace(incoming / f'{key}.json')
    return key, request


def wait_receipt(key, request, spool=SPOOL, timeout=900):
    deadline = time.monotonic() + timeout
    receipt = spool / 'results' / f'{key}.json'
    while time.monotonic() < deadline:
        if receipt.exists():
            result = json.loads(receipt.read_text())
            if (result.get('source_commit') != request['head_sha'] or
                    result.get('archive_sha256') != request['sha256']):
                raise ValueError('Publication receipt does not match this export')
            if result['status'] != 'success':
                raise RuntimeError(result.get('error', result['status']))
            print(json.dumps(result), flush=True)
            return result
        time.sleep(2)
    raise TimeoutError('Local publisher did not confirm a healthy deployment within 15 minutes')


def main():
    info = context(os.environ)
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() != info['head_sha']:
        raise ValueError('Checkout differs from the Actions source commit')
    if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no']):
        raise ValueError('Tracked source changed during export')
    key, request = stage(Path('_site'), info)
    print(f'Local export {key} queued; waiting for Hong Kong health checks', flush=True)
    result = wait_receipt(key, request)
    if summary := os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(summary, 'a') as stream:
            stream.write(f"Direct publication verified: https://math.opensii.ai/blueprint/\n\n"
                         f"Source: `{result['source_commit']}`; no GitHub website artifact transfer.\n")


if __name__ == '__main__':
    main()
