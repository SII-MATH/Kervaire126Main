# Kervaire 126 Blueprint

The Blueprint is one native hgraph project with eight chapters: SpectralSequence, AdamsSynthetic, Literature, E2Computation, ProofTools, AdamsCalculations, Main, and Geometry. The main document is English and organized by mathematical content. Geometry states the dimension-126 existence result and complete dimension classification; its literature assumptions and unfinished source-to-model bridges remain documented in Literature and in the Lean obligation registry.

## Native dependency and proof-state behavior

`scripts/build-blueprint.py` calls the pinned hgraph synchronizer and site generator directly. The synchronizer reads the original Lean files and authored `\lean`, statement `\uses`, and proof `\uses` annotations. Many-to-many bindings, label aliases, informal statements, proof blocks, `\leanok`, `\mathlibok`, warning reporting, reconciliation and closure all follow native hgraph behavior.

The displayed dependency graph contains the authored mathematical dependencies only. There is no compiler-derived graph projection, all-bindings dependency rule, transitive reduction, paper/fallback union, exact group coverage, duplicate `decl:` correspondence registration, hidden-obligation state rewriting, independent source/frontend closure oracle, evidence seed, source fingerprint gate, or fatal-warning policy. Dependency changes in a Lean proof do not automatically rewrite the mathematical graph. Native warnings are reported in `native-sync.json` and do not by themselves prevent export.

Native states describe hgraph's source-local formalization evidence and closure along authored `uses` edges. A successful website export is not a Lean compilation or a verification of transitive compiled proof dependencies. The Lean interface locks, permitted-hole registry and full repository trust checks remain separate and continue to run under `lake build`.

The only repository additions to native graph semantics are the two retained boundaries in `scripts/blueprint_boundaries.py`:

- Every Lean-bound entry may bind only public interface-lock exports actually defined in its chapter's mathematical module. Namespace spelling and the location of consumers do not determine ownership. A binding must match the mathematical object or conclusion stated in the entry.
- Cross-chapter statement and proof dependencies must point to an earlier chapter. Dependencies within one chapter use native hgraph behavior; no additional statement-level cycle policy is imposed by the exporter.

These boundaries inspect authored bindings and dependencies. They do not generate edges, add declarations, or change proof states. The native map is enabled by `site.map: true` and consumes the native project payload directly; no separate map graph or map dependency validator is generated.

ProofTools presents the substantive revised theorems, representative calculus, finite-window comparisons and the zero-layer nu-cofiber bridge. Shared notation and local proof steps appear with the results that use them. Main states its detection conditions together and explains the retained contradiction argument in Proposition 7.9's proof. The other chapters use the same mathematical granularity: shared notation and elementary steps accompany their definitions or calculations, while actual tower, label and representative comparisons retain their stated ranges and pending construction boundaries. The public Lean API is broader than these displayed mathematical entries; an exported declaration need not have its own Blueprint node. Some bound declarations retain an `Internal` namespace from their source organization; public status is determined by the explicit modifier and interface lock. No alias parser adapter or manual proof-state override is used.

## Authoring and provenance

- `blueprint/content.tex` defines the eight-chapter reading order. Each chapter is authored directly in `blueprint/chapters/<Module>.tex`, with sections organized by mathematical content. Definitions, literature statements, revisions and derived results appear together in their chapter; provenance is stated at each entry.
- Titles, statements and bindings are independent of proof completion or consumer patterns. Existing `paper:...`, `sem:...` and `frontier:...` labels remain stable references, not separate levels or groups. A single permanence node retains the aliases for Theorems 1.4 and 7.1. Original source material remains available under `AimPaper/`; source locators and citations supply provenance and diagram rendering without imposing an additional correspondence registry.
- All authored entries may use native statement and proof dependencies. A mathematical prerequisite need not consume every Lean declaration bound to its target.
- Write informal proofs in a separate `\begin{proof} ... \end{proof}` immediately after the theorem-like environment. The native reader turns these into collapsible Proof panels; inline “Proof.” paragraphs and proof environments nested inside statements do not provide that presentation. All 47 displayed AimPaper results have a proof panel, including literature specializations and explicitly qualified source arguments where a recorded gap remains. Definitions do not need proofs. Adding prose does not discharge Lean obligations or change formalization status.
- `% Blueprint note:` and `% Correspondence:` explanations are published as ordinary native node comments. The note adapter preserves human comments and does not add bindings, dependency edges or proof states.
- Paper commutative diagrams are rendered directly from their original TeX; a presentation copy retains lists, primes, citations and source links. This conversion does not alter bindings or dependencies. It does not modify the pinned hgraph implementation or frontend.
- References to imported statements, notation and numbered equations use native hgraph navigation within the reader, including equations in proof panels. Referenced standalone TikZ figures are rendered from AimPaper with their original captions and displayed inline. Source-text fallback links are reserved for material absent from the Blueprint; explicit provenance and original-proof links remain available.

Source paragraphs use `From \cite{key}, Theorem 6.1.` for quoted statements and equivalent restatements, including changes of notation. Statements with modified hypotheses, domains or specified comparisons use `A ... revision of \cite{key}, Theorem 6.1.`, with a description such as `level-indexed` or `finite-layer`. Spell out locators such as `Theorem`, `Proposition` and `Corollary`, and present the attribution as a plain paragraph before the statement. Keep proof-method attribution and any pending source-to-model comparisons explicit; the source wording does not certify those comparisons.

`corrections.yaml` remains the sole authored record of corrections relative to AimPaper. The native AimPaper corrections tab renders that record and reads revised statements from the native project payload. Scope notes and unfinished mathematical bridges remain in the Lean sources, the registry and the authored explanations. Reading links do not create mathematical dependencies or claim proof completion. See [the correction authoring guide](../docs/corrections.md).

The **Proposals** section of the native **Interfaces** tab presents independent agent interface reports from tracked `interface/proposals/<module>/<id>/report.md` files. It supports full-report search, module/status filters, report downloads and review feedback for agents to write back to the same record. Existing archived reports retain their original approval scope and evidence limits. Export does not require the local archive or change formal interfaces, mathematical dependencies or proof states. See [the proposal guide](../docs/interface-proposals.md).

The native **Interfaces** tab presents the eight public interface locks, generated exports, registered obligations, audit boundaries and identifier renames directly from `interface/baselines/`. An Overview-style status summary groups named public interfaces by completed proofs, locally complete proofs whose baselines still permit dependency gaps, direct obligations, and definitions or objects. Source-local flags and declaration kinds come from the native Lean parser; baseline axiom allowances are not a fresh dependency audit. Status and module counts open the matching declaration list; registry links include private responsibilities. Search and module filters operate on a derived export; original baselines remain the only source and can be downloaded unchanged. Source statements and local context come from the native Lean parser, before elaboration. The **Baselines** and **Proposals** sections share this single native tab, with links from declarations to matching reports and from reports to their module baseline. Neither section adds mathematical nodes, changes proof states, or certifies a Lean build. See [the baseline guide](../docs/metadata-baselines.md).

Within a project, hgraph lazily retains up to six recent main views and three overlays, restoring reading positions, expanded content and graph/map controls. Hidden React views suspend their effects; least-recently-used views are evicted. Interfaces retains its two internal sections on first use, so returning to Baselines does not refetch the data or discard filters. Caches reset on project changes or document refresh; refresh reads the current export without relying on persistent browser storage.

Generated hgraph nodes, edges, web presentation copies and `_site/` are reproducible outputs. Existing native comments and reviews remain attached to their nodes. Historical compiler evidence and retired graph-import material belong under ignored `local-history/`, not in the active export pipeline. The old implementation-index and verification web pages remain retired.

## Meeting task tab

The native **Meeting** custom tab displays the October 13 meeting's original
T01–T27 tasks, their current status, owners, merge targets and source links.
`meeting/2026-10-13.yaml` is the authored record; update it when a task changes.
The exporter derives the counts and page from that record. Merged tasks retain
their original IDs and link to the receiving task, without counting twice in
the follow-up total. All meeting discussion items, including T13, use the same
discussion status and count toward the follow-up total. The tab supports
status filters and search and is exported with the existing native website
pipeline. Optional task `details` sections hold completion explanations or meeting discussion material,
code excerpts and `code` references (`file` and `declaration`); the exporter
links these to the current declaration lines in the published sources. A task's
optional `details_label` names its expandable panel.
Meeting statuses do not modify mathematical entries or proof states.

## Installation and export

Use the hgraph revision pinned in `requirements-blueprint.txt`; the Lean toolchain and dependency lock are unchanged.

```sh
python3 -m venv .lake/blueprint-env
.lake/blueprint-env/bin/pip install -r requirements-blueprint.txt
.lake/blueprint-env/bin/python scripts/build-blueprint.py
```

`scripts/publish-blueprint.py` is an equivalent export entry point. Neither entry point needs a previously compiled snapshot, a successful full build, a downloaded evidence seed, or a Lean cache. The export writes native frontend assets, source links, the corrections tab, `native-sync.json`, and an informational `publication.json`. It does not write a compiler-verification report.

To verify Lean independently:

```sh
python3 scripts/check-source-inventory.py
lake build
```

To test the native integration and retained boundaries:

```sh
.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'
```

## Preview and publication

```sh
python3 scripts/serve-blueprint.py --port 18726
```

The default address is `http://127.0.0.1:18726/#/Kervaire126`. `scripts/preview-memo.py` creates an isolated Memo presentation preview from an existing native export; it does not recompile Lean or change mathematical dependencies or proof states. Browser checks under `Tests/check_blueprint_*.py` exercise the actual native reader, formulas, original diagrams and built-in map.

GitHub Pages exports `main` with the same native workflow. Its Python runtime and diagram tools are independent of Lean CI; no compiled-evidence release or Lean build cache is needed to publish. See [GitHub Pages](../docs/github-pages.md). Git pushes and pulls still follow the separate Release build-cache rules in `AGENTS.md`.
