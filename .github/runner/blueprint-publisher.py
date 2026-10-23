#!/usr/bin/env python3
"""Root-owned local export handoff and direct publication to Hong Kong.

Install this reviewed file as ops/blueprint/publisher.py. Never execute a copy
from the job's writable checkout as root. GitHub is queried for run identity and
successful export steps only; website bytes never go through GitHub storage.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import pwd
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.request

HERE = Path(__file__).resolve().parent
OPS = HERE.parent
STATE = HERE / 'runtime'
REPO = 'SII-MATH/Kervaire126Main'
BASE = 'https://math.opensii.ai/blueprint/'
REMOTE = '/srv/kip126-blueprint'
SPOOL = Path('/var/lib/kip126-blueprint-publish')
MAX_ARCHIVE = 512 * 1024**2
REQUIRED_STEPS = {'Test native synchronization and retained chapter boundaries',
                  'Export authored Blueprint with native hgraph',
                  'Include native live-server project snapshot'}


class NotReady(Exception):
    """GitHub step metadata may lag the local export completion."""


def atomic_json(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.chmod(0o644)
    temporary.replace(path)


def setup_spool():
    user = pwd.getpwnam('kip-web')
    for path in (SPOOL, SPOOL / 'incoming', SPOOL / 'results', STATE / 'queue'):
        if path.is_symlink():
            raise ValueError('Publication spool must not be a symlink')
        path.mkdir(parents=True, exist_ok=True)
        os.chown(path, user.pw_uid if path.name == 'incoming' else 0,
                 user.pw_gid if path.name == 'incoming' else 0)
        path.chmod(0o700 if path.name in {'incoming', 'queue'} else 0o755)


def read_regular(path, maximum):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as stream:
        metadata = os.fstat(stream.fileno())
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > maximum:
            raise ValueError('Invalid local handoff file')
        data = stream.read(maximum + 1)
        if len(data) > maximum:
            raise ValueError('Oversized local handoff file')
        return data


def validate_request(request, key):
    if (not isinstance(request, dict) or request.get('repository') != REPO or
            type(request.get('id')) is not int or type(request.get('run_attempt')) is not int or
            not re.fullmatch(r'[1-9][0-9]{0,19}-[1-9][0-9]{0,5}', key) or
            key != f"{request['id']}-{request['run_attempt']}" or
            not re.fullmatch('[0-9a-f]{40}', request.get('head_sha', '')) or
            not re.fullmatch('[0-9a-f]{64}', request.get('sha256', '')) or
            type(request.get('bytes')) is not int or not 0 < request['bytes'] <= MAX_ARCHIVE):
        raise ValueError('Invalid local publication request')
    return request


def verify_run(request):
    rid, attempt = request['id'], request['run_attempt']
    info = api(f'actions/runs/{rid}')
    if (info['head_sha'] != request['head_sha'] or info['run_attempt'] != attempt or
            info['head_branch'] != 'main' or info['head_repository']['full_name'] != REPO or
            info['path'] != '.github/workflows/pages.yml' or
            info['event'] not in {'push', 'workflow_dispatch'} or
            info['status'] not in {'in_progress', 'completed'} or
            info['conclusion'] not in {None, 'success'}):
        raise ValueError('Publication request is not a current main export')
    jobs = api(f'actions/runs/{rid}/attempts/{attempt}/jobs?per_page=100')['jobs']
    for job in jobs:
        if (job['name'] == 'Export main Blueprint' and job['runner_name'] == 'inspire-kip126-web-01' and
                job['conclusion'] in {None, 'success'}):
            passed = {step['name'] for step in job['steps'] if step['conclusion'] == 'success'}
            if REQUIRED_STEPS <= passed:
                return
    raise NotReady('Waiting for successful tests, export and runtime steps')


def capture(key):
    """Copy runner-owned files into a root-owned, restart-safe queue before use."""
    queue = STATE / 'queue' / key
    if queue.exists():
        return
    request = validate_request(json.loads(read_regular(SPOOL / 'incoming' / f'{key}.json', 4096)), key)
    with tempfile.TemporaryDirectory(prefix='.capture-', dir=STATE / 'queue') as td:
        td = Path(td)
        source = SPOOL / 'incoming' / f'{key}.tar'
        fd = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        digest, total = hashlib.sha256(), 0
        with os.fdopen(fd, 'rb') as stream, (td / 'site.tar').open('wb') as output:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                raise ValueError('Website archive is not a regular file')
            for chunk in iter(lambda: stream.read(1024**2), b''):
                total += len(chunk)
                if total > MAX_ARCHIVE:
                    raise ValueError('Oversized website archive')
                digest.update(chunk)
                output.write(chunk)
            output.flush()
            os.fsync(output.fileno())
        if total != request['bytes'] or digest.hexdigest() != request['sha256']:
            raise ValueError('Local website archive checksum mismatch')
        atomic_json(td / 'request.json', request)
        td.rename(queue)


def receipt(key, request, **result):
    atomic_json(SPOOL / 'results' / f'{key}.json', {
        'source_commit': request.get('head_sha'), 'archive_sha256': request.get('sha256'),
        **result})


def prepare_activation(request):
    # Recheck immediately before changing current: cancellation or newer main
    # must not let an older job overwrite a newer publication.
    verify_run(request)
    if api('commits/main')['sha'] != request['head_sha']:
        raise ValueError('Export superseded by a newer main commit; awaiting its export')

def run(args, **kw):
    return subprocess.run(args, check=True, text=True, timeout=600, **kw)

def api(path):
    return json.loads(run(['gh', 'api', f'repos/{REPO}/{path}'], capture_output=True).stdout)

def ssh_args():
    paths = run(['bash', '-c', '. "$1/lib/paths.sh"; printf "%s\\n%s\\n" "$MATH_PORTAL_KEY" "$MATH_PORTAL_KNOWN_HOSTS"', '_', str(OPS)], capture_output=True).stdout.splitlines()
    return ['ssh', '-i', paths[0], '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=15', '-o', 'StrictHostKeyChecking=yes', '-o', f'UserKnownHostsFile={paths[1]}']

def extract(archive, target):
    target.mkdir(exist_ok=True)
    with tarfile.open(archive, mode='r|*') as tf:
        seen = set()
        total = 0
        for member in tf:
            p = Path(member.name)
            if (p.is_absolute() or '..' in p.parts or '\\' in member.name or p in seen or
                    not (member.isfile() or member.isdir()) or (not p.parts and not member.isdir())):
                raise ValueError(f'unsafe archive entry: {member.name}')
            seen.add(p)
            total += member.size
            if len(seen) > 100000 or total > 2 * 1024**3:
                raise ValueError('oversized website archive')
            destination = target / p
            if member.isdir():
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                with tf.extractfile(member) as source, destination.open('xb') as output:
                    shutil.copyfileobj(source, output)
    for p in target.rglob('*'):
        p.chmod(0o755 if p.is_dir() else 0o644)
    for name in ('index.html', 'Kervaire126/data.json'):
        if not (target / name).is_file():
            raise ValueError(f'missing website file: {name}')

def publish(run_info, archive):
    sha, rid = run_info['head_sha'], int(run_info['id'])
    if not re.fullmatch('[0-9a-f]{40}', sha):
        raise ValueError('invalid commit')
    attempt = run_info['run_attempt']
    release = f'{sha}-{rid}-{attempt}'
    with tempfile.TemporaryDirectory(prefix='publish-', dir=STATE) as td:
        td = Path(td)
        site = td / 'site'
        site.mkdir()
        extract(archive, site)
        marker = {'repository': REPO, 'source_commit': sha, 'run_id': rid,
                  'run_attempt': attempt, 'transport': 'local-direct-ssh',
                  'archive_sha256': run_info['sha256'],
                  'published_at': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
        (site / 'deployment.json').write_text(json.dumps(marker, indent=2) + '\n')
        ssh = ssh_args()
        native_enabled = run(ssh + ['root@150.5.147.42', 'systemctl is-enabled --quiet kip126-review && echo yes || true'], capture_output=True).stdout.strip() == 'yes'
        if native_enabled and not (site / '.hgraph-runtime/config.yaml').is_file():
            raise ValueError('native review service requires a runtime snapshot; refusing incomplete publication')
        run(ssh + ['root@150.5.147.42', f"test $(df -B1 --output=avail /srv | tail -1) -gt 268435456 && mkdir -p {REMOTE}/releases/{release}"])
        run(['rsync', '-az', '--chmod=D755,F644', '-e', shlex.join(ssh), str(site) + '/', f'root@150.5.147.42:{REMOTE}/releases/{release}/'])
        prepare_activation(run_info)
        previous = run(ssh + ['root@150.5.147.42', f'readlink {REMOTE}/current || true'], capture_output=True).stdout.strip()
        run(ssh + ['root@150.5.147.42', f'ln -sfnT releases/{release} {REMOTE}/next && mv -Tf {REMOTE}/next {REMOTE}/current'])
        try:
            # Feedback lives in /var/lib and is independent of the native snapshot.
            if (site / '.hgraph-runtime/config.yaml').is_file():
                run(ssh + ['root@150.5.147.42', 'if systemctl is-enabled --quiet kip126-review; then systemctl restart kip126-review; fi'])
            for attempt in range(30):
                try:
                    with urllib.request.urlopen(BASE + 'Kervaire126/project.json', timeout=30) as response: response.read(1)
                    break
                except Exception:
                    if attempt == 29: raise
                    time.sleep(2)
            with urllib.request.urlopen(BASE + 'deployment.json', timeout=30) as response:
                if json.load(response) != marker:
                    raise ValueError('public deployment marker mismatch')
            for path in ('', 'Kervaire126/data.json'):
                with urllib.request.urlopen(BASE + path, timeout=30) as response:
                    if response.status != 200:
                        raise ValueError('public health check failed')
        except Exception:
            if re.fullmatch(r'releases/[0-9a-f]{40}-[0-9]+(?:-[0-9]+)?', previous):
                run(ssh + ['root@150.5.147.42', f'ln -sfnT {previous} {REMOTE}/rollback && mv -Tf {REMOTE}/rollback {REMOTE}/current; if systemctl is-enabled --quiet kip126-review; then systemctl restart kip126-review; fi'])
            raise
        atomic_json(STATE / 'deployed.json', marker)
        # Delete only our strictly named old releases; always retain the previous good one.
        cleanup = """from pathlib import Path
import re, shutil
root=Path('/srv/kip126-blueprint')
keep={root.joinpath('current').resolve().name, %r}
for p in (root/'releases').iterdir():
 if re.fullmatch(r'[0-9a-f]{40}-[0-9]+(?:-[0-9]+)?', p.name) and p.name not in keep and p.is_dir() and not p.is_symlink(): shutil.rmtree(p)
""" % Path(previous).name
        try:
            run(ssh + ['root@150.5.147.42', 'python3 -c ' + shlex.quote(cleanup)])
        except subprocess.SubprocessError as error:
            print(f'Published successfully; old release cleanup needs retry: {error}', flush=True)
        print(json.dumps(marker), flush=True)
        return marker

def once():
    keys = {p.stem for p in (SPOOL / 'incoming').glob('*.json')} | {p.name for p in (STATE / 'queue').iterdir()}
    for key in sorted(keys):
        if not re.fullmatch(r'[1-9][0-9]{0,19}-[1-9][0-9]{0,5}', key):
            continue
        queue = STATE / 'queue' / key
        if (SPOOL / 'results' / f'{key}.json').exists():
            if queue.exists():
                shutil.rmtree(queue)
            for suffix in ('.tar', '.json'):
                (SPOOL / 'incoming' / (key + suffix)).unlink(missing_ok=True)
            continue
        request = {}
        try:
            capture(key)
            request = json.loads((queue / 'request.json').read_text())
            verify_run(request)
            deployed = json.loads((STATE / 'deployed.json').read_text()) if (STATE / 'deployed.json').exists() else {}
            if (request['id'], request['run_attempt']) < (deployed.get('run_id', 0), deployed.get('run_attempt', 1)):
                raise ValueError('Export superseded by a newer published run')
            if (deployed.get('run_id'), deployed.get('run_attempt'), deployed.get('archive_sha256')) == (
                    request['id'], request['run_attempt'], request['sha256']):
                # Recover a crash between the durable deployment marker and receipt.
                with urllib.request.urlopen(BASE + 'deployment.json', timeout=30) as response:
                    if json.load(response) != deployed:
                        raise ValueError('Previously deployed receipt differs from the live marker')
                marker = deployed
            else:
                marker = publish(request, queue / 'site.tar')
            receipt(key, request, status='success', deployment=marker)
        except (NotReady, subprocess.SubprocessError, OSError) as error:
            print(f'{key}: retrying local publication: {error}', flush=True)
            if queue.exists() and time.time() - queue.stat().st_mtime > 900:
                receipt(key, request, status='failed', error='Publication retries exceeded 15 minutes')
        except (ValueError, KeyError, TypeError, tarfile.TarError) as error:
            print(f'{key}: rejected local publication: {error}', flush=True)
            receipt(key, request, status='failed', error=str(error))

def main():
    STATE.mkdir(mode=0o700, parents=True, exist_ok=True)
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['start', 'stop', 'watch', 'once'])
    args = parser.parse_args()
    pidfile = STATE / 'publisher.pid'
    if args.command == 'stop':
        if pidfile.exists():
            pid = int(pidfile.read_text())
            try:
                if str(HERE / 'publisher.py').encode() in Path(f'/proc/{pid}/cmdline').read_bytes():
                    if os.getpgid(pid) == pid: os.killpg(pid, signal.SIGTERM)
                    else: os.kill(pid, signal.SIGTERM)
            except FileNotFoundError: pass
        return
    if args.command == 'start':
        setup_spool()
        with open(STATE / 'publisher.lock', 'a') as probe:
            try: fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError: return
        # Do not inherit developer/API secrets into a long-lived service.
        env = {'HOME': '/root', 'PATH': '/usr/local/bin:/usr/bin:/bin', 'LANG': 'C.UTF-8', 'https_proxy': 'http://127.0.0.1:7890', 'http_proxy': 'http://127.0.0.1:7890', 'no_proxy': '127.0.0.1,localhost,math.opensii.ai'}
        with open(STATE / 'publisher.log', 'a') as log:
            subprocess.Popen([sys.executable, str(HERE / 'publisher.py'), 'watch'], env=env, stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True, close_fds=True)
        return
    with open(STATE / 'publisher.lock', 'w') as lock:
        try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError: return
        if args.command == 'once': once()
        else:
            pidfile.write_text(str(os.getpid()))
            while True:
                try: once()
                except Exception as exc: print(f'{time.strftime("%FT%TZ", time.gmtime())}: {type(exc).__name__}: {exc}', flush=True)
                time.sleep(2)

if __name__ == '__main__': main()
