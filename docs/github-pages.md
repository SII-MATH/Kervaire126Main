# GitHub Pages deployment

The Pages deployment is configured for the `gh-pages` branch, served from its
repository root by GitHub's managed `pages-build-deployment` workflow.
The public Blueprint address is
<https://sii-math.github.io/Kervaire126Main/#/Kervaire126>.
The canonical mathematical development remains on `develop`.

The deployment branch retains the exact Lean sources and other source inputs
represented by the verified export. Static export files are copied to its root;
`pages-deployment.json` lists the generated roots and records provenance.
The root `.nojekyll` file requests direct static-file publication. Existing
authoring and source files are preserved. GitHub does not clone or install the
private hgraph dependency to generate this site.

## Preparing an update

Generate the export from the canonical source checkout using the existing
publication command described in [the Blueprint README](../blueprint/README.md):

```sh
.lake/blueprint-env/bin/python scripts/publish-blueprint.py
```

Use a separate `gh-pages` worktree. For subsequent updates, merge the intended
canonical `develop` commit normally, then check and restore a matching Release
cache as required by [AGENTS.md](../AGENTS.md). Canonical source files come from
that merge, never from `_site/`. Replace generated export content only within
the roots listed in `pages-deployment.json`, and update that provenance manifest.
Preserve all other files and do not overwrite canonical mathematical development.

Before committing, verify every source and site-input SHA recorded under
`validation.inputs` and `validation.site_inputs` against the deployment checkout.
Copy the original export evidence unchanged. The export's recorded source commit
may differ from the deployment commit: this is legitimate only when the recorded
input footprint still matches exactly. Never rewrite old validation evidence to
make it appear to have been generated from a newer commit.

Run the required checks in the deployment worktree:

```sh
python3 scripts/check-source-inventory.py
lake build
```

Commit and push normally, without force-pushing. GitHub then redeploys the branch.
In the same task, upload the successful deployment commit's `.lake/build/` cache
to a traceable GitHub Release, with `metadata.json` and SHA-256 checksums, following
[the repository cache rules](../AGENTS.md). The cache must represent that exact
committed source and environment; an uncommitted build cannot be labeled as the
deployment commit's cache. A failed upload must be reported explicitly.

The generated site retains its proof-status and verification reports. Publishing
an export does not discharge any pending mathematical proof obligation.
