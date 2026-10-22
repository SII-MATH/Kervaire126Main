#!/usr/bin/env python3
"""Root-owned supervisor for the independent Blueprint runner, without systemd."""
import fcntl
import grp
import json
import os
from pathlib import Path
import pwd
import shutil
import signal
import subprocess
import sys
import time

OPS = Path('/inspire/hdd/global_user/czxs25250150/ops')
PERSISTENT = OPS.parent / 'kip126-web'
CI_HOME = Path('/var/lib/kip126-web')
HERE = Path(__file__).resolve().parent
STATE = HERE / 'runtime'
USER = 'kip-web'
MEMORY_LIMIT = 16 * 1024**3


def processes(uid):
    result = []
    for proc in Path('/proc').glob('[0-9]*'):
        try:
            if proc.stat().st_uid == uid:
                fields = (proc / 'statm').read_text().split()
                result.append((int(proc.name), int(fields[1]) * os.sysconf('SC_PAGE_SIZE')))
        except (OSError, ValueError, IndexError):
            pass
    return result


def stop_children(uid):
    for sig, delay in ((signal.SIGTERM, 10), (signal.SIGKILL, 2)):
        for pid, _ in processes(uid):
            try:
                os.kill(pid, sig)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + delay
        while processes(uid) and time.monotonic() < deadline:
            time.sleep(.2)


def live():
    try:
        data = json.loads((STATE / 'status.json').read_text())
        cmd = Path('/proc', str(data['supervisor_pid']), 'cmdline').read_bytes()
        return data if str(HERE / 'blueprint-service.py').encode() in cmd and b'watch' in cmd else None
    except (OSError, ValueError, KeyError):
        return None


def watch():
    lock = (STATE / 'supervisor.lock').open('w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        return
    uid = pwd.getpwnam(USER).pw_uid
    stopping = False

    def stop(*_):
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    cpus = sorted(os.sched_getaffinity(0))[12:16] or sorted(os.sched_getaffinity(0))[:4]
    env = {
        'HOME': str(CI_HOME), 'USER': USER, 'LOGNAME': USER, 'LANG': 'C.UTF-8',
        'PATH': str(CI_HOME / 'tools/venv/bin') + ':/usr/local/bin:/usr/bin:/bin',
        'BLUEPRINT_TOOLS': str(CI_HOME / 'tools'), 'LEAN_NUM_THREADS': '2',
        'MATHLIB_NO_CACHE_ON_UPDATE': '1', 'TMPDIR': str(CI_HOME / 'tmp'),
        'https_proxy': 'http://127.0.0.1:7890', 'http_proxy': 'http://127.0.0.1:7890',
        'no_proxy': 'localhost,127.0.0.1',
        'ACTIONS_RUNNER_HOOK_JOB_STARTED': '/usr/local/lib/kip126-blueprint/job-start.sh',
        'DOTNET_GCHeapHardLimit': '0x40000000',
    }
    try:
        while not stopping:
            # Reap only this dedicated account's previous runner/job children.
            stop_children(uid)
            cmd = ['/usr/sbin/runuser', '-u', USER, '--', '/usr/bin/nice', '-n', '10',
                   '/usr/bin/ionice', '-c', '2', '-n', '7', '/usr/bin/taskset', '-c',
                   ','.join(map(str, cpus)), './run.sh']
            child = subprocess.Popen(cmd, cwd=CI_HOME / 'runner', env=env, start_new_session=True)
            while not stopping and child.poll() is None:
                rss = sum(size for _, size in processes(uid))
                data = {'supervisor_pid': os.getpid(), 'runner_parent_pid': child.pid,
                        'cpus': cpus, 'memory_watchdog_bytes': MEMORY_LIMIT,
                        'rss_bytes': rss, 'updated_at': time.time()}
                temporary = STATE / 'status.tmp'
                temporary.write_text(json.dumps(data))
                temporary.replace(STATE / 'status.json')
                if rss > MEMORY_LIMIT:
                    print('CI account exceeded 16 GiB RSS; stopping its processes', flush=True)
                    break
                time.sleep(5)
            stop_children(uid)
            try:
                child.wait(timeout=15)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
            if not stopping:
                time.sleep(10)
    finally:
        stop_children(uid)
        (STATE / 'status.json').unlink(missing_ok=True)


def main():
    if os.geteuid() != 0:
        raise SystemExit('Supervisor must run as root; runner jobs use the dedicated kip-web account')
    STATE.mkdir(mode=0o700, exist_ok=True)
    action = sys.argv[1]
    if action == 'watch':
        watch()
    elif action == 'start':
        if live():
            return
        try:
            pwd.getpwnam(USER)
        except KeyError:
            # The registration and workspace survive on GPFS if an image is restored.
            uid, gid = str(PERSISTENT.stat().st_uid), str(PERSISTENT.stat().st_gid)
            try:
                grp.getgrnam(USER)
            except KeyError:
                subprocess.run(['groupadd', '--system', '--gid', gid, USER], check=True)
            subprocess.run(['useradd', '--system', '--gid', USER, '--uid', uid,
                            '--home-dir', str(CI_HOME), '--shell', '/usr/sbin/nologin', USER], check=True)
        user = pwd.getpwnam(USER)
        CI_HOME.mkdir(parents=True, exist_ok=True)
        os.chown(CI_HOME, user.pw_uid, user.pw_gid)
        (CI_HOME / 'tmp').mkdir(exist_ok=True)
        os.chown(CI_HOME / 'tmp', user.pw_uid, user.pw_gid)
        runner = CI_HOME / 'runner'
        if not runner.exists():
            shutil.copytree(PERSISTENT / 'runner', runner)
            for directory, dirs, files in os.walk(runner):
                os.chown(directory, user.pw_uid, user.pw_gid)
                for name in files:
                    os.chown(Path(directory) / name, user.pw_uid, user.pw_gid)
        tools = CI_HOME / 'tools'
        if not (tools / 'toolchain.json').exists():
            tools.mkdir(exist_ok=True)
            subprocess.run(['/usr/bin/python3', '-m', 'venv', str(tools / 'venv')], check=True)
            source = next((PERSISTENT / 'tools/venv/lib').glob('python*/site-packages'))
            destination = next((tools / 'venv/lib').glob('python*/site-packages'))
            shutil.copytree(source, destination, dirs_exist_ok=True)
            shutil.copy2(PERSISTENT / 'tools/toolchain.json', tools / 'toolchain.json')
        if not (runner / '.runner').is_file():
            # Root restores only this slot's registration; the job account has
            # no permission to traverse the developer workspace parent.
            for name in ('.runner', '.credentials', '.credentials_rsaparams'):
                source = PERSISTENT / 'registration' / name
                if source.is_file():
                    shutil.copy2(source, runner / name)
                    os.chown(runner / name, user.pw_uid, user.pw_gid)
            if not (runner / '.runner').is_file():
                raise SystemExit('Runner registration is missing; configure it before starting')
        policy = Path('/usr/local/lib/kip126-blueprint')
        policy.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE / 'blueprint-job-start.py', policy / 'job-start.py')
        (policy / 'job-start.py').chmod(0o755)
        shutil.copyfile(HERE / 'blueprint-job-start.sh', policy / 'job-start.sh')
        (policy / 'job-start.sh').chmod(0o755)
        # Do not pass developer credentials or the shell environment to jobs.
        with (STATE / 'supervisor.log').open('a') as log:
            subprocess.Popen([sys.executable, str(HERE / 'blueprint-service.py'), 'watch'],
                             stdin=subprocess.DEVNULL, stdout=log, stderr=log,
                             start_new_session=True, close_fds=True,
                             env={'PATH': '/usr/local/bin:/usr/bin:/bin', 'LANG': 'C.UTF-8'})
    elif action == 'stop':
        data = live()
        if data:
            os.kill(data['supervisor_pid'], signal.SIGTERM)
            for _ in range(100):
                if not live():
                    break
                time.sleep(.2)
    elif action == 'status':
        print(json.dumps(live()))
    else:
        raise SystemExit('Usage: blueprint-service.py start|stop|status|watch')


if __name__ == '__main__':
    main()
