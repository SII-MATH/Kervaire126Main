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
contains only the generated public site, source links and native synchronization report.

## Publication and proof verification

Pages uses the pinned native hgraph synchronizer and site generator. Publication reads current authored mathematical `uses` annotations and original Lean source files. The only repository graph checks are same-module public bindings and cross-chapter dependency order. Native warnings remain warnings.

The workflow runs the Blueprint integration/presentation tests and exports the site directly. It does not install Lean, restore a Lean cache, download a compiled-evidence seed, refresh a compiler snapshot, infer mathematical dependencies from compiled proofs, or gate publication on a complete repository build. The native map reads the native project payload directly.

`native-sync.json` records the native synchronizer's result and warnings. `publication.json` describes the native export and retained chapter boundaries; it is not a compiler-verification report. A successful Pages run does not establish a successful Lean build or discharge any pending mathematical obligation. Lean compilation, interface locks and proof-hole checks remain in the independent CI workflow.

For local commands and native authoring behavior, see the [Blueprint README](../blueprint/README.md).

## Build caches

The [AGENTS.md Release cache rules](../AGENTS.md) still apply to every source
push and to source updates after a pull or merge. Synchronize a successful
commit-matching `.lake/build/` cache with traceable Release metadata and SHA-256
checksums in the same task. Actions dependency caches and the Pages artifact do
not replace that Release cache, and a failed full build cannot be labeled as a
successful commit cache. Report any cache synchronization failure explicitly.
