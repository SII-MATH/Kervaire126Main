# CI event coverage and cache reuse

CI keeps the existing Ubuntu runner, Lean thread count, toolchain, dependencies,
source-inventory check, and full `lake build`. No mathematical check or module is
removed. `Lean checks` remains the required PR/main check.

## Avoiding duplicate develop runs

PRs, main pushes and manual runs always build. A develop push builds too, unless
the exact same commit already heads an open PR from this repository to main.
That PR receives the full required check. A stale PR, another repository/base,
or a failed API query does not suppress the develop build. A race while opening
a PR may still produce two builds; coverage takes priority over deduplication.

Develop-push jobs are named `Develop checks`, so skipping one cannot publish a
skipped or successful result under the required PR check's name. Event selection
does not change branch protection, and API/setup failure retains a real build.

## Separate dependency and project caches

- `.lake/packages` uses an OS/architecture/toolchain/manifest key. It is not
  uploaded again for every project-source change on the same cache scope.
- `.lake/build` uses the same environment plus the complete Git tree. Exact,
  same-tree partial, then same-environment incremental baselines are tried.
- Successful project builds and best-effort partial failure builds remain
  distinct. A partial cache is never marked complete.

The old combined `v1` caches are left alone and expire normally. The first `v2`
run in a scope obtains the pinned imported Mathlib cache and seeds the split
caches. Dependency retrieval is governed by the dependency-cache result, not
the project-cache result. Every selected event still invokes full `lake build`.

## Cross-branch Release reuse

GitHub isolates Actions caches by branch/PR merge ref. CI therefore also checks
the repository's existing `build-cache-<commit>-<os>-<arch>` Releases when it
has no exact project-cache hit. It reads small metadata first and accepts only
a passed, clean build with the same repository, OS/architecture, toolchain,
manifest hash, and exact build-input manifest. This uses the existing Release
schema: tracked Lean files, dependency locks, metadata JSON and scripts,
including Git file modes and SHA-256 file contents.

Only an exact input match can replace an Actions incremental baseline. Missing,
incompatible, expired or corrupt releases leave that baseline intact and fall
back to rebuilding. CI checks metadata/manifests, each archive part and the
combined archive against SHA-256; it never selects merely the newest Release.
Discovery is bounded to eight platform-matching candidates from the first 30
Releases, preferring the current source commit. Network calls have timeouts and
the entire optional restore step has a five-minute ceiling.

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
fingerprints, single/split archives, incompatible metadata, checksum failure,
archive traversal/links/devices, active writers, and installation rollback.
