# Inspire Lean CI

Internal PRs, main/develop pushes, merge groups and manual CI jobs use the single
`kip126-inspire` runner. Fork PRs continue to use GitHub's Ubuntu runner. The
required check remains `Lean checks`; every selected build still runs the source
inventory check and full `lake build`, including the existing trust audits.

## Host and isolation

The runner runs as the dedicated, non-login Linux account `kip-ci`, with its own
home at `/inspire/hdd/global_user/czxs25250150/kip126-ci`. It has no developer GitHub
credentials. Its pinned Lean installation, runner registration, workspace and
all writable caches live under that home. The checkout links `.lake` only to its own persistent environment cache;
no dependency/build directory links to the development checkout. Bootstrap copies use independent files
or copy-on-write copies, never hard links.

The Lean runner has one executing job at a time. A separate main-only Blueprint runner uses a different account, workspace and four CPUs, so webpage exports do not wait for Lean PR jobs. The Lean process tree
inherits a 12-logical-CPU affinity, nice level 10 and best-effort I/O
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

The checkout links `.lake` to
`~/cache/environments/<toolchain-and-lock>/`.
The single slot reuses this same project build across commits, PRs and merge
groups. Lake checks the current source and dependencies and incrementally rebuilds
affected modules. Source/input fingerprints do not select another working cache,
copy a baseline or trigger a Release download. Partial build progress is retained.
Builds are serial; the directory is private to this CI account and never links to
development caches. Another toolchain or lock selects another environment.

Migration from the old `inputs/<fingerprint>` layout renames the active build
within the same filesystem, preserving its files and inodes. An older environment
build is retained under a `build.before-single-slot-*` name when necessary.
No project cache is copied. Other old input snapshots are left untouched.

Only a missing project build triggers exact-input Release bootstrap. A populated
working cache is always left for Lake to validate; recovery of a damaged cache
requires preserving/moving it first, without active writers. Release metadata,
input fingerprints and archive checksums remain strict. Every selected event
still runs full `lake build` and existing trust audits. Release publication and
sync remain required by `AGENTS.md`; the single CI working cache is not itself a
claim that the newly checked-out source has already passed.

A successful Mathlib cache operation is recorded by toolchain, lock and imported
module set. Import headers come from Lean's native `--deps-json` parser and are
cached by each source file's content, toolchain, lock and parser implementation.
Only changed/new files invoke Lean again; removal or movement recomputes which
imports are external. No handwritten import parser is used. Repeated jobs check
recorded `.olean` paths directly, without starting Lake or searching every
package. Old success markers are upgraded after artifact checks. New imports,
another lock or a missing imported artifact cause the normal cache fetch again.
Python policy/cache tests retain their full coverage and use private temporary
directories under local `/tmp`, avoiding GPFS metadata traffic for throwaway
fixtures. Persistent project and dependency caches remain under the dedicated
account's environment directory.

Toolchain changes require provisioning the newly approved pinned toolchain before
the runner can build it; this deployment does not upgrade project dependencies.

## Network and restart

The runner initiates outbound HTTPS via `http://127.0.0.1:7890`. No incoming port,
public IP or GitHub webhook is needed. The existing host proxy watchdog is a
prerequisite. A proxy outage makes the runner unavailable until it reconnects.

The root-owned deployment is `/inspire/hdd/global_user/czxs25250150/ops/ci-runner/`.
It contains copies of `.github/runner/service.py`, `job-start.sh` and
`job-start.py`. The shell entry point and Python policy are installed under
`/usr/local/lib/kip126-ci/`. Updating the repository
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

## Independent Blueprint export slot

`kip126-blueprint` is registered separately as `inspire-kip126-web-01` and runs
as the non-login `kip-web` account under `/var/lib/kip126-web/`. Only the root supervisor reads its persistent
registration/tool backup under `kip126-web/`; the job account gains no access
to the developer workspace parent. Its root-owned admission
hook accepts only `pages.yml` pushes or manual exports on `main`; it rejects PRs,
forks, other branches and other workflows. Its process tree uses four CPUs away
from the Lean slot, nice 10, I/O priority 7 and a 16 GiB RSS watchdog.

The fixed hgraph commit `c33cf070fb664360e8822fd2834b39d15ebd8d8e`,
PyYAML 6.0.1 and TeX/Graphviz tools are provisioned once. The Python environment is root-owned under
`/opt/kip126-blueprint-tools`, outside the job account's writable home. The export job retains the native content-addressed diagram cache across checkouts,
verifies the fixed tools and performs no apt, pip, Python-setup or hgraph checkout during publication.
The independent root supervisor and existing instance watchdog restore the slot
after runner failure or restart. Exported files pass through a local handoff to
the root-owned publisher and directly over SSH to Hong Kong, with no GitHub
artifact upload or download. Safe extraction, atomic release switching and
health/rollback checks remain, and the job waits for the live publication receipt;
public feedback remains outside website releases.

Host supervisor: `ops/blueprint-runner/blueprint-service.py`. Registration and
runtime credentials are never committed. Tool upgrades require explicit
provisioning and a repository pin change; ordinary exports do not update them.
