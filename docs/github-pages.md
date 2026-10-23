# Blueprint publication on the Hong Kong VPS

`main` is the sole publication source. A push to `main`, or a manual Actions
dispatch for `main`, generates the Blueprint on our local independent runner and
publishes it directly to the Hong Kong VPS.
The public site is [Blueprint](https://math.opensii.ai/blueprint/#/Kervaire126).
Changes reach `main` through the protected PR and merge queue workflow.

The export hands a SHA-256 checked archive to the root-owned local publisher
through `/var/lib/kip126-blueprint-publish/incoming`. The publisher snapshots it
into its own persistent queue, verifies the main Actions run and successful test,
export and runtime steps, validates archive paths and file types, and transfers
the generated files directly over SSH. It checks main again before activation to
reject superseded or cancelled exports. GitHub supplies code, PRs and task
coordination; no website artifact is uploaded to or downloaded from GitHub.
GitHub operator credentials and the SSH key remain outside the job account.

The workflow waits for a root-owned receipt matching its source and archive hash.
It succeeds only after the public health checks pass. A network failure is retried
from the persistent queue; a publisher process restart retains captured work.
Failed checks roll back the website and fail publication. A newer main commit
supersedes an older export; the newer commit's job publishes the current source.

Caddy serves `/blueprint/` directly from `/srv/kip126-blueprint/current` without
portal authentication. Publication uploads a new release directory, atomically
switches `current`, verifies the public deployment marker and project data, and
keeps the previous good release for rollback. Existing portal authentication on
other routes is preserved. The site remains available when the development
machine is offline; new publication resumes when its watchdog starts the publisher.
`deployment.json` identifies the actual export commit, Actions run and attempt,
archive hash, and `local-direct-ssh` transport.

The reviewed publisher source is `.github/runner/blueprint-publisher.py`; install
it as `ops/blueprint/publisher.py` on the operator host. Repository checkout does
not automatically update root-owned operational code. The separate control-plane
directory documents restart, rollback and route installation. The VPS
does not run Lean or build the website. Old GitHub Pages links should be updated
to the address above; the Pages host is no longer the publication target.

## Public hgraph dependency

The independent runner uses the exact `SII-MATH/hgraph` revision pinned in
`requirements-blueprint.txt`, preinstalled under root-owned
`/opt/kip126-blueprint-tools`. It verifies this environment before every export;
ordinary publication does not install dependencies. The local handoff contains
the generated public site, source links, native synchronization report and the
native review server's immutable project snapshot. Public feedback is stored
separately on the VPS and never included in website replacement.

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
