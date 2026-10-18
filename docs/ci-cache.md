# CI event coverage and cache reuse

CI keeps the existing Ubuntu runner, Lean thread count, toolchain, dependencies,
source-inventory check, and full `lake build`. No mathematical check or module is
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
- `.lake/build` uses the same environment plus the complete Git tree. Exact,
  same-tree partial, then same-environment incremental baselines are tried.
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
has no exact project-cache hit. It reads small metadata first and accepts only
a passed, clean build with the same repository, OS/architecture, toolchain,
manifest hash, and exact build-input manifest. This uses the existing Release
schema: tracked Lean files, dependency locks, metadata JSON and scripts,
including Git file modes and SHA-256 file contents.
Both the original sorted-file-list manifest and the fingerprint-envelope
manifest are accepted. In either format the complete file list must match the
checkout exactly, in addition to the metadata fingerprint and checksum checks.

Only an exact input match can replace an Actions incremental baseline. Missing,
incompatible, expired or corrupt releases leave that baseline intact and fall
back to rebuilding. CI checks metadata/manifests, each archive part and the
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
replace verification. The required local push/pull Release synchronization
policy remains in force; this workflow consumes those releases but does not
claim that Actions caching publishes them.

## Validation

```sh
python3 -m unittest discover -s Tests -p 'test_ci_cache.py'
python3 scripts/check-source-inventory.py
lake build
```

The Python tests cover event coverage, stale/foreign PRs, API failure, input
fingerprints, shallow merge parents, paginated discovery beyond the old cutoff,
discovery timeouts/API failures, single/split archives, incompatible metadata, checksum failure,
archive traversal/links/devices, active writers, and installation rollback.
