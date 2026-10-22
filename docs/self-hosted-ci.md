# Inspire Lean CI

Internal PRs, main/develop pushes, merge groups and manual CI jobs use the single
`kip126-inspire` runner. Fork PRs continue to use GitHub's Ubuntu runner. The
required check remains `Lean checks`; every selected build still runs the source
inventory check and full `lake build`, including the existing trust audits.

## Host and isolation

The runner runs as the dedicated, non-login Linux account `kip-ci`, with its own
home at `/inspire/hdd/global_user/czxs25250150/kip126-ci`. It has no developer GitHub
credentials. Its pinned Lean installation, runner registration, workspace and
all writable caches live under that home. No dependency/build directory is
symlinked to the development checkout. Bootstrap copies use independent files
or copy-on-write copies, never hard links.

There is one registered runner and thus one executing job at a time. Its entire
process tree inherits a 12-logical-CPU affinity, nice level 10 and best-effort I/O
priority 7. Lean uses four threads per process. A root supervisor samples the
dedicated account's aggregate RSS every five seconds and terminates its processes
if they exceed 64 GiB. This is a watchdog, not a kernel-enforced memory cgroup;
brief overshoot is possible. The container currently has a 54-core CPU quota and
300 GiB memory limit. These limits leave capacity for normal development and
must be reassessed if the container allocation changes.

The host's root-owned pre-job hook allows only this repository's `ci.yml`,
same-repository PRs, main/develop pushes, main merge groups and manual CI runs.
It rejects forks, `pull_request_target`, unrelated workflows and missing event
data before checkout. Workflow routing also keeps fork PRs on GitHub. A workflow
condition alone is not the security boundary. Repository writers remain trusted:
their jobs can access this dedicated account's state, including its runner
registration. They cannot write root-owned host policy or developer files.

## Persistent cache

Checkout retains `.lake` and removes other untracked files before the Lean job.
The toolchain and dependency lock identify a cache environment. On an environment
change, the previous `.lake` is archived under `~/cache/environments/` rather than
reused as a current environment. Within one environment, Lake validates traces
and rebuilds changed inputs and their dependents. Partial compilation survives
cancellation without an upload/download round trip. Hosted jobs retain the
existing Actions/Release restoration path.

The local runner does not automatically replace its incremental cache with a
Release on every job. Release cache publication and verification required by
`AGENTS.md` still apply to pushes; local persistence does not replace that policy.
Toolchain changes require provisioning the newly approved pinned toolchain before
the runner can build it; this deployment does not upgrade project dependencies.

## Network and restart

The runner initiates outbound HTTPS via `http://127.0.0.1:7890`. No incoming port,
public IP or GitHub webhook is needed. The existing host proxy watchdog is a
prerequisite. A proxy outage makes the runner unavailable until it reconnects.

The root-owned deployment is `/inspire/hdd/global_user/czxs25250150/ops/ci-runner/`.
It contains copies of `.github/runner/service.py` and `job-start.py`; the latter
is installed at `/usr/local/lib/kip126-ci/job-start.py`. Updating the repository
does not automatically change the host security policy.

The existing `ops/instance-autostart.sh` starts this supervisor only for the
selected development machine and stops it when the machine loses that role or
services are drained. The supervisor restarts a failed runner, and the existing
instance watchdog recreates a failed supervisor. Notebook startup sources the
existing shell bootstrap, which starts that watchdog. Persistent registration,
workspace and toolchain survive a container restart; start recreates the service
account and host hook if necessary. A new container must retain the existing
bootstrap and be selected as the development machine before it can run CI.

Root administration:

```sh
python3 /inspire/hdd/global_user/czxs25250150/ops/ci-runner/service.py status
python3 /inspire/hdd/global_user/czxs25250150/ops/ci-runner/service.py stop
python3 /inspire/hdd/global_user/czxs25250150/ops/ci-runner/service.py start
```

Stop interrupts an active CI job; use the existing ops drain mode for maintenance
and confirm GitHub reports the runner idle before planned work. Supervisor state
and logs are under `ops/ci-runner/runtime/`; runner diagnostics are under
`kip126-ci/runner/_diag/`. Registration files and credentials must never enter Git.
