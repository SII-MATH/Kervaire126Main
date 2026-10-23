# CI event coverage and cache reuse

Internal jobs use the isolated Inspire self-hosted runner described in
[self-hosted CI](self-hosted-ci.md); fork PRs retain the hosted Ubuntu runner.
CI keeps the pinned toolchain, dependencies, source-inventory check, and full
`lake build`. No mathematical check or module is
removed. `Lean checks` remains the required PR/main check.

## Avoiding duplicate develop runs

PRs, main pushes, merge groups and manual runs always build. A develop push builds too, unless
the exact same commit already heads an open PR from this repository to main.
That PR receives the full required check. A stale PR, another repository/base,
or a failed API query does not suppress the develop build. A race while opening
a PR may still produce two builds; coverage takes priority over deduplication.

Develop-push jobs are named `Develop checks`, so skipping one cannot publish a
skipped or successful result under the required PR check's name. Event selection
does not change branch protection, and API/setup failure retains a real build.

## Main merge queue

CI handles `merge_group: checks_requested` for `main` as well as pull requests.
Every queue group runs the same required `Lean checks`, source inventory, cache
checks and full `lake build` against GitHub's combined merge-group commit. The
event planner never suppresses a merge-group build or looks it up as a develop
PR. Concurrency includes the event name and PR number or full ref: separate
queue groups, ordinary PRs and main pushes cannot cancel each other's checks.

`.github/merge-queue-ruleset.json` records the repository ruleset applied to
`refs/heads/main`: no bypass actors, `ALLGREEN`, merge commits, at most two
concurrent queue builds, at most two PRs merged together, a minimum of one PR
with no batching delay, and a 120-minute check timeout. These settings retain
all required checks for every queued PR. The classic branch protection keeps
its required GitHub Actions `Lean checks`, PR requirement and administrator
enforcement. Its strict up-to-date flag is disabled only after the merge queue
is active, since the queue validates the current main plus preceding PRs.

The existing App-authenticated auto-merge workflow detects whether the base
branch has a queue. With a queue it uses `gh pr merge --auto` without selecting
a merge strategy, so GitHub queues the PR when its initial requirements pass.
Without a queue it retains the existing merge-commit behavior. It never uses
`--admin`, executes PR source or automatically resolves conflicts. A failed or
conflicting queue group is removed by GitHub and must be fixed before re-entry.

Apply the workflow support to main before activating the ruleset. The ruleset
can be maintained through the repository rules API from the checked-in JSON;
keep the existing branch protections when updating it. Official references:
[merge queue configuration](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue)
and [merge-group events](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#merge_group).

## Separate dependency and project caches

- `.lake/packages` uses an OS/architecture/toolchain/manifest key. It is not
  uploaded again for every project-source change on the same cache scope.
- On the self-hosted single slot, `.lake/build` persists per toolchain and lock,
  across source changes; Lake performs incremental validation without copying it.
  On hosted runners, the complete Git tree selects exact, same-tree partial, then
  same-environment incremental Actions baselines.
- Successful project builds and best-effort partial failure builds remain
  distinct. A partial cache is never marked complete.

The old combined `v1` caches are left alone and expire normally. The first `v2`
run in a scope obtains the pinned imported Mathlib cache and seeds the split
caches. Every run incrementally fetches the currently imported Mathlib roots,
even after a dependency-cache hit: the environment key stays unchanged when a
new module imports additional libraries. Existing cached files are reused.
Every selected event still invokes full `lake build`.

## Cross-branch Release reuse

GitHub isolates Actions caches by branch/PR merge ref. CI therefore also checks
the repository's existing `build-cache-<commit>-<os>-<arch>` Releases when it
has no project build on the self-hosted slot, or no exact Actions project-cache hit on a hosted runner. It reads small metadata first and accepts only
a passed, clean build with the same repository, OS/architecture, toolchain,
manifest hash, and exact build-input manifest. This uses the existing Release
schema: tracked Lean files, dependency locks, `interface/baselines/` JSON and scripts,
including Git file modes and SHA-256 file contents.
Both the original sorted-file-list manifest and the fingerprint-envelope
manifest are accepted. In either format the complete file list must match the
checkout exactly, in addition to the metadata fingerprint and checksum checks.

Only an exact input match can replace an Actions incremental baseline. Missing,
incompatible, expired or corrupt releases leave that baseline intact and fall
back to rebuilding. CI checks interface/baselines/manifests, each archive part and the
combined archive against SHA-256; it never selects merely the newest Release.
Discovery first probes the current commit and its direct parents by their exact
Release tags. This finds the incoming PR head's cache for a synthetic merge-group
commit even when that Release is absent from the first listing page. Parent IDs
come from the raw commit object, which retains them in a depth-one checkout.

If those probes miss, discovery paginates Releases (100 per page), checking all
platform-matching candidates within a 90-second discovery budget. Each page is
ordered by publication time rather than relying on the API's list order; there
is no eight-candidate/first-page cutoff. Tags are deduplicated. Logs identify
each metadata probe, incompatible inputs, discovery failures and time-budget
exhaustion. A cache hit still requires all compatibility and integrity checks;
publication time only determines search order. Network calls have timeouts and
the entire optional restore step retains its five-minute ceiling.

Extraction is streamed to a temporary directory. Paths outside `.lake/build`,
links, duplicate members, devices and excessive expansion are rejected. The
existing cache is backed up only after verification, active Lean/Lake writers
block installation, and an installation failure rolls back. Restoration is
restricted to the fresh CI workspace before compilation. It does not modify
the shared development worktree or its in-progress builds.

CI always runs the full build after restoration; Release metadata does not
replace verification. Release publication is asynchronous and main-only; Actions caching does not
publish Releases and no PR or push must wait for a fresh cache.

## Asynchronous main Release publication

A separate root-owned local service polls GitHub every 15 seconds. It observes
only `main` push runs of `ci.yml`, confirms the repository and run attempt, and
requires successful `Lean checks`, source inventory and full `lake build` on
`inspire-kip126-01`. PRs, merge-group runs, develop and failed/cancelled runs cannot
publish. The service is outside the required CI jobs, so pushing, merging and task
delivery never wait for archive creation or upload. It uses the existing operator
GitHub authentication; credentials are never passed into the runner job.

The durable pending request follows the newest main SHA, with a 60-second quiet
period to coalesce bursts. Pending older commits are superseded; a release already
uploading may finish before the next main is handled. A populated CI cache is read
only while the slot is idle and its checkout matches the successful build. If a
new CI job starts or the checkout/cache changes, the unfinished capture is rejected
and retried. It takes no CI lock and never copies or writes the working cache.
Only the immutable verified artifact is uploaded after capture, so CI can run
while uploads proceed. If the checkout has moved to a PR, publication waits for a
successful latest-main checkout; rerun CI on main if immediate publication is
needed. It never rebuilds another checkout just to publish a cache.

Existing compatible Releases are verified and reused. New bundles retain the
actual source commit, complete committed-input comparison, GitHub build log,
environment metadata, safe archive member validation and every file's SHA-256.
The compressed artifact is uploaded in 32 MiB parts. A draft becomes public only
after all expected assets match their server SHA-256 and sizes. Retries resume
the same draft and retain correct parts, uploading only missing/damaged expected
assets. Published caches are immutable. A persistent queue retries failures after
30 seconds, 2 minutes, 5 minutes, then every 15 minutes; successful main CI remains
successful. Service and partial upload state survive restart. Missing new Releases
never block pull/update: keep a local cache or use a verified same-environment old
baseline and run full `lake build`.

Install reviewed copies of `.github/runner/cache-publisher.py`,
`scripts/release-cache.py`, and `scripts/ci-cache.py` together in
`ops/cache-publisher/`, owned by root and inaccessible for job writes. Never run
publisher modules from the job-writable checkout. The instance watchdog starts
and stops this independent service alongside the CI supervisor; it needs no extra
GitHub runner, incoming port, or webhook. Capture/compression runs on two CPUs,
nice 15 and I/O priority 7. Its state, receipts and log live in `runtime/`.

```sh
python3 /inspire/hdd/global_user/czxs25250150/ops/cache-publisher/cache-publisher.py status
python3 /inspire/hdd/global_user/czxs25250150/ops/cache-publisher/cache-publisher.py retry
python3 /inspire/hdd/global_user/czxs25250150/ops/cache-publisher/cache-publisher.py start
python3 /inspire/hdd/global_user/czxs25250150/ops/cache-publisher/cache-publisher.py stop
```

A status of `debouncing`, `waiting` or `publishing` is pending, not synced;
`retrying` includes the next attempt and error. `published`/`reuse` requires a
verified Release receipt. The watchdog restarts a dead service; `retry` requests
an immediate retry without changing the queue concurrently.

## Validation

```sh
python3 -m unittest discover -s Tests -p 'test_ci_cache.py'
python3 -m unittest discover -s Tests -p 'test_async_release_cache.py'
python3 scripts/check-source-inventory.py
lake build
```

The Python tests cover event coverage, stale/foreign PRs, API failure, input
fingerprints, shallow merge parents, paginated discovery beyond the old cutoff,
discovery timeouts/API failures, single/split archives, incompatible metadata, checksum failure,
archive traversal/links/devices, active writers, and installation rollback.
