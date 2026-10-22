# Blueprint publication on the Hong Kong VPS

`main` is the sole publication source. A push to `main`, or a manual Actions
dispatch for `main`, generates the Blueprint and uploads a static website artifact.
The public site is [Blueprint](https://math.opensii.ai/blueprint/#/Kervaire126).
Changes reach `main` through the protected PR and merge queue workflow.

The host-owned publisher on the Inspire development machine polls successful
`Export main Blueprint` jobs every minute, downloads the `github-pages` artifact,
validates its archive paths and file types, and uploads it over SSH to the Hong Kong
VPS. The artifact name is retained for compatibility; GitHub Pages deployment and
Pages permissions are no longer used. GitHub credentials and the SSH key remain
on the operator host, outside the CI runner and GitHub Actions jobs.

Caddy serves `/blueprint/` directly from `/srv/kip126-blueprint/current` without
portal authentication. Publication uploads a new release directory, atomically
switches `current`, verifies the public deployment marker and project data, and
keeps the previous good release for rollback. Existing portal authentication on
other routes is preserved. The site remains available when the development
machine is offline; new publication resumes when its watchdog starts the publisher.
`deployment.json` identifies the actual export commit and Actions run.

Operational source lives in the separate `ops/blueprint/` control-plane directory.
That directory also documents restart, rollback and route installation. The VPS
does not run Lean or build the website. Old GitHub Pages links should be updated
to the address above; the Pages host is no longer the publication target.

## Public hgraph dependency

The workflow checks out the exact public `SII-MATH/hgraph` revision pinned in
`requirements-blueprint.txt`. No cross-repository secret or deploy key is needed.
The checkout is outside the cached `.lake/` directory; the Python virtual
environment is under `RUNNER_TEMP`. Neither is included in caches or the website artifact. The artifact
contains only the generated public site, source links and native synchronization report.

## Publication and proof verification

The export uses the pinned native hgraph synchronizer and site generator. Publication reads current authored mathematical `uses` annotations and original Lean source files. The only repository graph checks are same-module public bindings and cross-chapter dependency order. Native warnings remain warnings.

The workflow runs the Blueprint integration/presentation tests and exports the site directly. It does not install Lean, restore a Lean cache, download a compiled-evidence seed, refresh a compiler snapshot, infer mathematical dependencies from compiled proofs, or gate publication on a complete repository build. The native map reads the native project payload directly.

`native-sync.json` records the native synchronizer's result and warnings. `publication.json` describes the native export and retained chapter boundaries; it is not a compiler-verification report. A successful export run does not establish a successful Lean build or discharge any pending mathematical obligation. Lean compilation, interface locks and proof-hole checks remain in the independent CI workflow.

For local commands and native authoring behavior, see the [Blueprint README](../blueprint/README.md).

## Build caches

The [AGENTS.md Release cache rules](../AGENTS.md) still apply to every source
push and to source updates after a pull or merge. Synchronize a successful
commit-matching `.lake/build/` cache with traceable Release metadata and SHA-256
checksums in the same task. Actions dependency caches and the website artifact do
not replace that Release cache, and a failed full build cannot be labeled as a
successful commit cache. Report any cache synchronization failure explicitly.

## Changing repository visibility

This repository belongs to the `SII-MATH` organization. GitHub Team supports
protected branches and rulesets in private organization repositories; retaining
GitHub's **native merge queue** for a private organization repository requires
**GitHub Enterprise Cloud**. The current Free plan cannot retain both protections
when switching this repository to private. Hosting and self-hosted CI do not
change these plan requirements. Do not switch visibility until the chosen plan
and existing protection/ruleset settings have been verified.

Before and after a visibility change, export and compare the `main` branch
protection, active merge-queue ruleset, required `Lean checks` app binding,
workflow permissions and runner access. Verify a real PR through the queue.
The static site continues to publish generated Lean source pages, interface
baselines and proposal attachments publicly; making the Git repository private
does not make those exported files private.

References: [protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches),
[merge queue availability](https://docs.github.com/en/enterprise-cloud@latest/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue).
