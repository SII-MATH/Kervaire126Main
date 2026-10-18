# GitHub Pages

`main` is the sole publication source. A push to `main`, or a manual Actions
dispatch for `main`, generates the Blueprint, uploads a Pages artifact and
deploys it to <https://sii-math.github.io/Kervaire126Main/#/Kervaire126>.
Set the repository's **Settings → Pages → Source** to **GitHub Actions**.
Changes developed on `develop` reach the site through a normal pull request and
merge into `main`; no `gh-pages` branch or manually copied export is required.

## Public hgraph dependency

The workflow checks out the exact public `SII-MATH/hgraph` revision pinned in
`requirements-blueprint.txt`. No cross-repository secret or deploy key is needed.
The checkout is outside the cached `.lake/` directory; the Python virtual
environment is under `RUNNER_TEMP`. Neither is included in caches or the Pages artifact. The artifact
contains only the generated public site and its verification/provenance data.

## Publication and proof verification

Page publication runs independently of the complete Lean CI build. It first
attempts to refresh compiled evidence for all mathematical source modules using
the existing publisher's `--refresh-source-evidence` mode. If that refresh fails,
publication uses the checked evidence seed and the publisher's normal scoped
verification mode. Changed declarations without matching compiled evidence
remain explicitly unverified. A failed export or failed provenance validation
prevents deployment; fallback is not permission to invent successful evidence.

The site preserves the distinction between the current publication source and
the earlier compiled baseline. Source fingerprints, `validation.json` and
deployment metadata identify their respective snapshots and checks. Do not
rewrite baseline commit IDs, hashes or recorded build results to match a newer
publication commit. A successful Pages run does not assert that the complete
repository built, nor discharge any pending mathematical proof obligation.

When the declared source inventory has changed since the fixed evidence seed, refresh the seed from a successful full `scripts/build-blueprint.py` run using `scripts/blueprint-pages.py pack-seed --output blueprint-evidence.tar.gz`. Publish that immutable archive with its SHA-256 checksum and update the workflow pin. The packer requires matching current mathematical inputs, kernel capture, interface/obligation coverage and a successful preceding full-build log. Preserve the original seed and its recorded source commit; do not relax declaration-coverage checks to consume an obsolete seed.

For local authoring and publication commands, see the
[Blueprint README](../blueprint/README.md). Inspect the Pages Actions run and the
published verification report when checking an update; a successful source push
alone does not establish a successful deployment.

## Build caches

The [AGENTS.md Release cache rules](../AGENTS.md) still apply to every source
push and to source updates after a pull or merge. Synchronize a successful
commit-matching `.lake/build/` cache with traceable Release metadata and SHA-256
checksums in the same task. Actions dependency caches and the Pages artifact do
not replace that Release cache, and a failed full build cannot be labeled as a
successful commit cache. Report any cache synchronization failure explicitly.
