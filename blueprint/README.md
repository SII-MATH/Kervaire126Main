# Kervaire 126 Blueprint

The Blueprint is one native hgraph project, written in English and organized into eight chapters: SpectralSequence, AdamsSynthetic, Literature, E2Computation, ProofTools, AdamsCalculations, Main, and Geometry. The computation layer is divided into algebraic $E_2$ input and later Adams calculations, consumed through their respective public entries. The former `KIP126.Computation` import paths have been removed; existing declaration names remain unchanged. Geometry records the three geometric conclusions and bridges that are not yet formalized.

The main document presents mathematical definitions and results, with related Lean declarations grouped under one entry where their scope permits. It does not count every private implementation lemma as a separate mathematical statement. The main navigation includes AimPaper corrections and Blueprint map. The map is an optional native hgraph modal, enabled by `site.map: true` in `hgraph/config.yaml`. Closing it preserves the reading view, selected statement, filters and scroll position without reloading. Its renderer and lifecycle API live in the pinned hgraph distribution; this project exports only a derived map data snapshot for inspection and standalone use. The retired implementation-index and verification web pages are no longer generated or linked. Declaration bodies, source locations, compiled dependencies and unfinished responsibilities remain in the Lean sources, internal graph, capture evidence and obligation registry.

## Authoring and provenance

**AimPaper corrections** uses the native `site.tabs` interface in `hgraph/config.yaml`, with `content: MEMO.md` pointing directly to the tracked root document. hgraph converts Markdown and typesets formulas using its native content page; no project-authored page renderer is involved. The staged export workspace links the same root file, and the memo participates in the site input fingerprint. Edit `MEMO.md` directly. Its relative links retain their authored targets. The separate concordance page has been removed; all original paper statements, formal correspondences and source exports remain part of the Blueprint.

- `blueprint/content.tex` and `blueprint/chapters/` define the eight-chapter structure and reading order.
- `blueprint/semantic/` contains the curated mathematical entries. Use native theorem/definition environments, stable `\label` values and `\lean` bindings to actual public interfaces. A binding identifies an object defined or a result asserted by that entry; it does not list background objects, hypotheses, pre-existing predicates used to express a result, or supporting proof steps. Multiple bindings are appropriate only when the prose states their respective mathematical content. Reference other mathematical entries in prose; the exporter derives dependency edges and completion states from compiled evidence. Do not manually assert completion with `\leanok`.
- `blueprint/paper/` contains all 57 original AimPaper definitions and results, preserved verbatim between their provenance markers. Mathematical titles identify their content; citation prefixes precede the statements, for example `(From [article], Theorem 7.1.)`. Other literature inputs identify their cited source and locator in the same way. Correspondence status is hidden authoring metadata (`% Correspondence:`), and partial correspondences retain native `\sketch` markers.
- `blueprint/frontier/` supplies mathematical titles and statements for the remaining public construction and proof groups. The generator requires exact coverage and exact public Lean bindings for the compiled groups; it rejects missing members, private bindings, ambiguous names and manually asserted completion. Private construction and proof obligations remain in the Lean sources, internal dependency graph and obligation registry.
- `% Blueprint note:` paragraphs preserve formal scope, implementation provenance and unproved bridges. The importer publishes these as native node comment attachments, outside the mathematical statement. Chapter-wide notes apply to their entries, and synchronization preserves human comments.
- `blueprint/generated/`, generated hgraph node/edge Markdown and `_site/` are reproducible outputs. Maintain mathematical prose in the authored files.

AimPaper has 42 bound entries, including 11 partial correspondences, and 15 entries without a direct formal binding. Three of the latter form the Geometry chapter. Theorem 2.12, Corollary 2.15, Proposition 5.10, Lemma 7.16 and Corollary 7.18 retain their partial scope notes, but their supporting lemmas and goal predicate are not bindings of the stated conclusions. A completed bound declaration does not by itself establish every condition of a more general paper statement; its native scope attachment and Lean type retain that distinction. Explicit declaration dependencies resolve public paper bindings to stable source identities; they cannot authorize a private binding.

Every Lean-bound entry must bind only exports in the interface lock of the chapter named after its actual source module. Paper entries, Main remarks and generated frontiers have no private-binding exception. The exporter checks the compiled source file, rather than the declaration namespace or the location of its consumers. This rule applies equally to semantic, paper and frontier entries and is checked again on the complete generated document. Cross-module dependencies are allowed; cross-module formal bindings are rejected. In particular, second-page labels belong to E2Computation, their later differential assertions to AdamsCalculations, synthetic spheres and page-extension definitions to AdamsSynthetic, and sphere-comparison isomorphisms to Literature. Generic filtered extension relations remain in SpectralSequence; synthetic specializations and crossing operations bind only their own local counterparts.

The native bibliography retains all 60 records from `AimPaper/main.bib`. AimPaper uses its original key `LWX126`; `00-primary-paper.bib` places that reference first through native same-key deduplication. Each paper entry cites it, providing bibliography backlinks. The article's original text, line anchors, PDF and bibliography are exported alongside the site. Original spectrum conventions, including 2-completion, connectivity and finite type, remain relevant.

Literature entries carry concise source prefixes: the attribution type, a primary reference and its most direct locator. Use at most two essential references or locators for a genuinely composite statement. `From` identifies original text; `Adapted from` identifies an adaptation; project constructions and related sources retain an honest attribution type. Keep scope restrictions, pending comparisons, grading conventions, adaptation steps, source versions and supplementary locators exclusively in native scope comments. The 38 inputs in the combined classical/synthetic comparison entry each have their own concise attribution. A `Detailed source attribution` note retains the full attribution when the visible prefix is shortened. Additional primary references live in `literature-sources.bib`; the original AimPaper bibliography and its 57 raw statement blocks remain unchanged. Checking a source does not complete a Lean proof or establish a pending identification with the project's selected objects.

Keep a source prefix in its own paragraph with `\par{}` followed by a blank line. The empty TeX group preserves the paragraph separator in the pinned frontend, whose cleanup otherwise removes whitespace immediately following `\par`.

Mathematical prose and its hidden scope notes are maintained in the authored TeX rather than duplicated in contract/source JSON files. Fixed upstream code versions are bibliography entries in `source-snapshots.bib`, linked from the native provenance attachments. The 125 former interface capability descriptions and six module convention notes also remain native node comment attachments under `hgraph/nodes/<id>/`. They describe related interface scope; they do not assert equivalence with broader paper statements or mark proofs complete. Full migration records and original JSON snapshots are local archives.

## Dependencies and unfinished work

The implementation graph retains every captured source declaration. Compiler-generated helpers are traversed to recover dependencies between actual source declarations; external libraries are not expanded into project tasks. Private declarations are identified by their compiled names and scoped source identities, rather than by an ambiguous short name.

The mathematical view projects this graph onto the authored entries and generated construction/proof frontier entries. The initial migration preserves all 299 existing registered obligations. An unfinished public producer may share a frontier entry with another public producer only when they have the same module, responsibility kind and exact consumer incidence. This incidence includes both displayed mathematical entries and unfinished producers themselves, so dependencies between unfinished producers cannot disappear during grouping. Unverified declarations remain explicitly unverified and are not treated as new proof obligations.

Every projected entry is checked against the actual compiled dependency closure, both in the complete native graph and in the entry-only graph used by the native frontend. Removing implementation nodes from the main statement count must never turn an upstream-dependent result green. The reading order separates algebraic $E_2$ input from the proof tools and from later Adams calculations. Paper entries follow the stage containing their actual formal counterparts, preserving every original label, statement, citation and scope qualification. Chapter aggregation is checked against the compiled mathematical dependency projection; the display must not conceal a genuine reverse dependency. Interface locks, the obligation registry and existing build checks remain authoritative.

The internal source graph records exact declaration-local completion. In the mathematical view, local completion also requires all private implementation ancestors to be complete: a registered private hole contributes `sorry`, and unverified private evidence contributes `empty`. These statuses are computed from the complete source graph, with the exact internal source identities retained as audit metadata rather than formal bindings. Public frontier dependencies are still shown as ordinary mathematical edges. No private obligation is dropped from the registry, and independent public results retain their own status. The native `lean_ok` status describes this mathematical local completion. `closed` requires all transitive dependencies to be complete; `formalized_open` means a locally completed entry still depends on unfinished work. `ready` and `blocked` describe unfinished entries and their prerequisites. Native Summary's “Ready now” uses the local status of direct prerequisites, whereas native CLI analysis uses transitive closure; machine-readable validation evidence records the counts. Statement counts, frontier-group counts and unique unfinished-producer counts are reported separately.

The external BX criterion (`paper:7.3`) belongs to Literature and binds only its two Literature interfaces. Main retains its existing fixed-system normalization and choice-transport theorem. Remarks 7.4 and 7.5 appear separately in Main with short mathematical proofs and bindings to the public interfaces `KIP126.Main.normalized_quotient` and `KIP126.Main.lambda_eta_theta_square_independent`. Their supporting page, filtration and detector calculations remain private. Public semantic interfaces retain their API-only binding rule. A prose reference between entries is a reading link; dependency edges come from the compiled bindings. The current final permanence theorem uses the distinguished-choice Literature interfaces directly, without depending on the exported any-choice theorem.

Corollary 1.5 binds the complete local proof `KIP126.Main.adams_two_line_classification`, with its exact target and actual-page list retained as separate definitions. Main assembles the unbounded E2 basis, corrected d2-stage candidate screening, nine newly authorized Literature inputs and the existing h5/h6 permanence theorems. The original ten new responsibilities became eleven after the user-approved source correction: nine in Literature, one in E2Computation and one in AdamsCalculations. The total registered responsibility count is now 310. Main adds no proof hole or caller premise, and local kernel completion does not close the upstream obligations. The original proof's E3 list omitted h0 h4: Lin Theorem 1.3(1) makes its d2 zero, and IWX Table 6, p. 222, records its nonzero d3. The public candidate predicate now includes it, and Main supplies the fourth mixed-product exclusion through the separate Literature input `iwx_h0_h4_d3`. The final survivor list and public Main theorem type are unchanged. All square indices remain third-page candidates; HHR supplies their later cutoff.

The new second-line entries follow the same concise source-prefix and native scope-comment conventions as the other entries. The E2 basis cites its original Adams 1960 Theorem 2.5.1(2), rather than Lin's later recollection. May's topology results cite the independently inspected 1964 thesis under `MayThesis1964`; the original AimPaper key `Maythesis` refers to a distinct 1966 algebra paper and is preserved unchanged. Directly checked IWX computations, their classical chart data and the classical localization comparison are identified separately from historical Mahowald--Tangora attribution and any unavailable original scan. Source review does not discharge the registered fixed-model proofs.

## Installation and full generation

Run from the repository root. Python dependencies are pinned separately from the existing Lean/Lake toolchain. The private SII-MATH/hgraph repository requires GitHub read access; for GitHub CLI credentials, run `gh auth setup-git --hostname github.com` before installing:

```sh
python3 -m venv .lake/blueprint-env
.lake/blueprint-env/bin/pip install -r requirements-blueprint.txt
.lake/blueprint-env/bin/python scripts/build-blueprint.py
```

The full generator runs the source-inventory checks, Blueprint tests and complete `lake build`, captures the compiled environment with `scripts/BlueprintCapture.lean`, validates the mappings and dependency projection, and exports the site. Matching capture checkpoints may be reused only when their input fingerprints and payload hashes agree. Input changes during capture or export abort that run rather than mixing snapshots.

Logs and capture evidence are in `.lake/blueprint/`. The exported `_site/validation.json` records the source snapshot, input fingerprints, build results and scope of the checks. A working-tree snapshot is not presented as the build cache of a pushed commit.

## Publishing while other proofs are in progress

```sh
.lake/blueprint-env/bin/python scripts/publish-blueprint.py
```

Publication is separate from the complete repository build. This entry point reuses verified declaration evidence, publishes the current mathematical authoring and citations, and independently builds and captures newly required support modules. An unrelated whole-project build failure does not prevent publication. Changed or unverifiable source declarations receive an explicit unverified state; a lexical scan that finds no `sorry` cannot make them complete. Initial publication requires a previously verified declaration snapshot.

Machine-readable validation evidence distinguishes reused evidence, scoped verification and the latest full-build result. Publication does not claim that the current entire repository builds. A completed full build can update only the build evidence in `validation.json` without changing mathematical data or the Blueprint map:

```sh
.lake/blueprint-env/bin/python scripts/publish-blueprint.py --refresh-build-report
```

After source files move, refresh their compiled evidence explicitly:

```sh
.lake/blueprint-env/bin/python scripts/publish-blueprint.py --refresh-source-evidence
```

This builds and captures every mathematical source module through the same scoped-verification pipeline. Audit consumers remain separate; an audit file containing a named mathematical declaration cannot be excluded. Stable source identities, all registered holes and both dependency closures are still checked. A failed full repository build remains recorded in `validation.json` and is never reported as passing by this command.

Do not replace the compiled importer with a standalone lexical `hgraph sync`: it cannot reliably resolve scoped private declarations or certify dependency closure.

## Preview and checks

```sh
python3 scripts/serve-blueprint.py
# Open http://127.0.0.1:18726/#/Kervaire126

.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'
python3 scripts/check-source-inventory.py
lake build
.lake/blueprint-env/bin/python Tests/check_blueprint_formulae.py --url http://127.0.0.1:18726/
.lake/blueprint-env/bin/python Tests/check_blueprint_map.py --url http://127.0.0.1:18726/
```

The formula check needs Playwright and Chromium; `--chromium` selects an installed browser. It strictly rerenders all paper formulas with the frontend's actual KaTeX bundle and checks red unknown commands as well as rendering errors. LaTeX with the article's packages and `dvisvgm` are needed to export its seven original XY diagrams. Display compatibility is applied to a generated TeX copy, leaving the checked original statement blocks unchanged.

Native CLI queries remain available from the repository root:

```sh
.lake/blueprint-env/bin/hgraph list --type tex --state ready --json
.lake/blueprint-env/bin/hgraph list --type implementation --json
```

The Overview, Summary, dependency graph, native map, Lean panels and review interface use the pinned private [SII-MATH/hgraph](https://github.com/SII-MATH/hgraph) distribution (Apache-2.0; based on AxelDlv00/hgraph, revision in `requirements-blueprint.txt`). Map is disabled by default in the library and enabled explicitly by this project. Custom project tabs may use `presentation: modal`; inline close buttons use `data-hgraph-close`, while same-origin iframe pages load `hgraph-custom-page.js` and call `hgraph.close()`. The host validates frame identity, origin and protocol version; see the fork's `docs/CUSTOM_PAGES.md`. Native comments and review attachments under `hgraph/nodes/<id>/` remain maintainable; synchronization preserves human-authored fields and attachments. The static preview can prepare GitHub issue submissions, which the user submits explicitly.

No mathematical interface, Lean dependency lock or proof responsibility is changed by this presentation. Compact metadata retains all existing type/universe/trust/export checks, exact permitted-hole fingerprints and Main/ProofTools boundary checks; see [metadata baselines](../docs/metadata-baselines.md). Historical prose and generated declaration payloads are archived instead of duplicated in those baselines.
