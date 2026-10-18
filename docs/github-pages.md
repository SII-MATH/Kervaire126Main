# GitHub Pages

`main` is the sole publication source. A push to `main`, or a manual Actions
dispatch for `main`, generates the Blueprint, uploads a Pages artifact and
deploys it to <https://sii-math.github.io/Kervaire126Main/#/Kervaire126>.
Set the repository's **Settings → Pages → Source** to **GitHub Actions**.
Changes developed on `develop` reach the site through a normal pull request and
merge into `main`; no `gh-pages` branch or manually copied export is required.

## Private hgraph access

The workflow checks out the exact private `SII-MATH/hgraph` revision pinned in
`requirements-blueprint.txt`. Configure a dedicated SSH deploy key:

1. Add its public key to `SII-MATH/hgraph` under **Settings → Deploy keys**,
   with write access disabled.
2. Add its private key to this repository's Actions secrets as
   `HGRAPH_DEPLOY_KEY`.

Do not commit either private credentials or substitute personal credentials.
The private checkout is outside the cached `.lake/` directory; the Python virtual
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
