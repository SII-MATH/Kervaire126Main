#!/usr/bin/env python3
"""Installed, root-owned main-only Release publisher, independent of CI jobs.

Install reviewed copies of this file, scripts/release-cache.py and
scripts/ci-cache.py in ops/cache-publisher. Never import job-writable code as root.
"""
import argparse
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
STATE = HERE / 'runtime'
ROOT = Path('/inspire/hdd/global_user/czxs25250150/kip126-ci/runner/_work/Kervaire126Main/Kervaire126Main')
REPO = 'SII-MATH/Kervaire126Main'
QUIET_SECONDS = 60
POLL_SECONDS = 15
RETRY_SECONDS = (30, 120, 300, 900)
SHA = re.compile('[0-9a-f]{40}')


class Deferred(Exception):
    """CI takes priority; this is not a failed publication attempt."""


def atomic_json(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def read_json(path, default=None):
    return json.loads(path.read_text()) if path.exists() else default


def api(endpoint):
    data = subprocess.check_output(['gh', 'api', f'repos/{REPO}/{endpoint}'],
                                   stderr=subprocess.PIPE, timeout=45)
    return json.loads(data)


def eligible_run(run, head):
    return (SHA.fullmatch(head) is not None and run.get('head_sha') == head and
            run.get('head_branch') == 'main' and run.get('event') == 'push' and
            run.get('path') == '.github/workflows/ci.yml' and
            run.get('head_repository', {}).get('full_name') == REPO and
            run.get('status') == 'completed' and run.get('conclusion') == 'success' and
            type(run.get('id')) is int and type(run.get('run_attempt')) is int)


def build_job(jobs):
    for job in jobs:
        passed = {s.get('name') for s in job.get('steps', []) if s.get('conclusion') == 'success'}
        if (job.get('name') == 'Lean checks' and job.get('conclusion') == 'success' and
                job.get('runner_name') == 'inspire-kip126-01' and
                {'Check source inventory', 'Build all modules and checks'} <= passed):
            return job
    raise ValueError('Main CI lacks the successful full build on the expected isolated runner')


def observe(queue, head, now):
    if not SHA.fullmatch(head):
        raise ValueError('Invalid main SHA')
    if queue.get('head_sha') != head:
        return {'head_sha': head, 'observed_at': now, 'ready_after': now + QUIET_SECONDS,
                'next_retry': 0, 'attempts': 0, 'status': 'debouncing'}
    return queue


def failed(queue, error, now):
    attempts = queue.get('attempts', 0) + 1
    return {**queue, 'attempts': attempts, 'status': 'retrying', 'error': str(error)[:2000],
            'next_retry': now + RETRY_SECONDS[min(attempts - 1, len(RETRY_SECONDS) - 1)]}


def runner_busy():
    # Local worker detection prevents waiting for delayed GitHub busy metadata.
    import pwd
    uid = pwd.getpwnam('kip-ci').pw_uid
    for proc in Path('/proc').glob('[0-9]*'):
        try:
            if proc.stat().st_uid == uid and (proc / 'comm').read_text().strip() == 'Runner.Worker':
                return True
        except OSError:
            continue
    return False


def load_publisher():
    spec = importlib.util.spec_from_file_location('release_cache', HERE / 'release-cache.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_guard(source):
    last_checked = [0.0]

    def check(force=False):
        if not force and time.monotonic() - last_checked[0] < 1:
            return
        last_checked[0] = time.monotonic()
        if runner_busy():
            raise Deferred('A CI job started; discard the unfinished capture and retry when idle')
        current = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], timeout=10).decode().strip()
        if current != source:
            raise Deferred('CI checkout changed; wait for the newest successful main build')
    return check


def capture_log(run, job, output):
    text = subprocess.check_output(['gh', 'run', 'view', str(run['id']), '--repo', REPO,
                                    '--job', str(job['id']), '--log'], stderr=subprocess.PIPE, timeout=90).decode()
    lines = []
    for line in text.splitlines():
        fields = line.split('\t', 2)
        if len(fields) == 3 and fields[1] == 'Build all modules and checks':
            lines.append(fields[2].split(' ', 1)[-1])
    text = '\n'.join(lines) + '\n'
    if not re.search(r'^Build completed successfully(?:\s|\.|$)', text, re.MULTILINE):
        raise ValueError('GitHub full-build log has no successful completion evidence')
    output.write_text(text)


def bundle_context(pub, directory):
    metadata = read_json(directory / 'metadata.json')
    inputs = read_json(directory / 'build-inputs.json')
    return {'root': ROOT, 'head': metadata['source_commit'], 'ci': pub.load_ci(ROOT),
            'inputs': inputs, 'toolchain': metadata['lean_toolchain'],
            'manifest_sha256': metadata['lake_manifest_sha256']}


def process(run, job):
    source = run['head_sha']
    output = STATE / 'builds' / source
    output.mkdir(parents=True, exist_ok=True)
    pub = load_publisher()
    # A verified immutable package survives retries/restarts even if CI moves on.
    packaged = read_json(output / 'package-result.json')
    if packaged:
        directory = Path(packaged['directory'])
        if directory != output / ('package-' + source):
            raise ValueError('Unexpected saved bundle location')
        current = bundle_context(pub, directory)
    else:
        guard = read_guard(source)
        guard(force=True)
        pub.CACHE_READ_GUARD = guard
        current = pub.snapshot(ROOT, source)
        log = output / 'lake-build.log'
        capture_log(run, job, log)
        args = SimpleNamespace(output=output, source_commit=source, build_log=log, build_exit_code=0)
        # Only this root-owned partial package is removed; never touch CI caches.
        partial = output / ('package-' + source)
        if partial.exists():
            import shutil
            if partial.is_symlink():
                raise ValueError('Unsafe partial package path')
            shutil.rmtree(partial)
        pub.package(args, current)
        reused = read_json(output / 'reuse-result.json')
        if reused:
            return reused
        packaged = read_json(output / 'package-result.json')
        directory = Path(packaged['directory'])
    if api('git/ref/heads/main')['object']['sha'] != source:
        raise Deferred('A newer main superseded this pending upload')
    # Only immutable artifact bytes are used from here. CI is free to run.
    pub.CACHE_READ_GUARD = None
    pub.publish(SimpleNamespace(output=output, package_dir=directory, release_id=None), current)
    result = read_json(output / 'publish-result.json') or read_json(output / 'reuse-result.json')
    if not result:
        raise ValueError('Publisher returned no verified Release receipt')
    return result


def once():
    now = time.time()
    queue = read_json(STATE / 'queue.json', {})
    head = api('git/ref/heads/main')['object']['sha']
    queue = observe(queue, head, now)
    atomic_json(STATE / 'queue.json', queue)
    if queue['status'] in {'published', 'reuse'}:
        return
    if now < max(queue['ready_after'], queue['next_retry']):
        return
    try:
        runs = api('actions/workflows/ci.yml/runs?branch=main&event=push&per_page=30')['workflow_runs']
        candidates = [r for r in runs if eligible_run(r, head)]
        if not candidates:
            raise Deferred('Waiting for successful main CI; PR and merge-group builds never publish')
        run = max(candidates, key=lambda r: (r['id'], r['run_attempt']))
        jobs = api(f"actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs?per_page=100")['jobs']
        job = build_job(jobs)
        queue.update(run_id=run['id'], run_attempt=run['run_attempt'], status='publishing', started_at=now)
        atomic_json(STATE / 'queue.json', queue)
        result = process(run, job)
        atomic_json(STATE / 'published.json', {**result, 'run_id': run['id'], 'run_attempt': run['run_attempt'],
                                             'finished_at': time.time()})
        queue.update(status=result['status'], finished_at=time.time(), result=result, error=None)
    except Deferred as error:
        queue.update(status='waiting', error=str(error), next_retry=time.time() + POLL_SECONDS)
    except Exception as error:
        queue = failed(queue, error, time.time())
        print(f'{head}: retrying publication: {type(error).__name__}: {error}', flush=True)
    atomic_json(STATE / 'queue.json', queue)


def live():
    info = read_json(STATE / 'service.json', {})
    try:
        return info if str(HERE / 'cache-publisher.py').encode() in Path('/proc', str(info['pid']), 'cmdline').read_bytes() else None
    except (OSError, KeyError):
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['start', 'stop', 'watch', 'once', 'status', 'retry'])
    command = parser.parse_args().command
    STATE.mkdir(parents=True, exist_ok=True, mode=0o700)
    if command == 'status':
        print(json.dumps({'service': live(), 'queue': read_json(STATE / 'queue.json', {}),
                          'published': read_json(STATE / 'published.json', {})}, indent=2))
        return
    if command == 'stop':
        if info := live():
            os.killpg(info['pid'], signal.SIGTERM)
        return
    if command == 'retry':
        # No concurrent queue writes: request is consumed by the worker.
        atomic_json(STATE / 'retry.json', {'requested_at': time.time()})
        return
    if command == 'start':
        if live():
            return
        config = STATE / 'gitconfig'
        config.write_text('[safe]\n\tdirectory = ' + str(ROOT) + '\n')
        env = {'HOME': '/root', 'PATH': '/usr/local/bin:/usr/bin:/bin', 'LANG': 'C.UTF-8',
               'GIT_CONFIG_GLOBAL': str(config), 'PYTHONDONTWRITEBYTECODE': '1',
               'http_proxy': 'http://127.0.0.1:7890', 'https_proxy': 'http://127.0.0.1:7890',
               'no_proxy': '127.0.0.1,localhost'}
        with (STATE / 'service.log').open('a') as log:
            subprocess.Popen(['/usr/bin/nice', '-n', '15', '/usr/bin/ionice', '-c', '2', '-n', '7',
                              '/usr/bin/taskset', '-c', ','.join(map(str, sorted(os.sched_getaffinity(0))[16:18] or sorted(os.sched_getaffinity(0))[:2])),
                              sys.executable, str(HERE / 'cache-publisher.py'), 'watch'],
                             env=env, stdin=subprocess.DEVNULL, stdout=log, stderr=log,
                             start_new_session=True, close_fds=True)
        return
    with (STATE / 'worker.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return
        atomic_json(STATE / 'service.json', {'pid': os.getpid(), 'started_at': time.time()})
        while True:
            try:
                if (STATE / 'retry.json').exists():
                    queue = read_json(STATE / 'queue.json', {})
                    if queue:
                        queue.update(next_retry=0, ready_after=0, status='waiting')
                        atomic_json(STATE / 'queue.json', queue)
                    (STATE / 'retry.json').unlink()
                once()
            except Exception as error:
                print(f'{time.strftime("%FT%TZ", time.gmtime())}: {type(error).__name__}: {error}', flush=True)
            if command == 'once':
                return
            time.sleep(POLL_SECONDS)


if __name__ == '__main__':
    main()
