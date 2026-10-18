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

ProofTools binds its representative, filtration, shift and zero-layer results directly to their actual public declarations. Some retain an `Internal` namespace from their source organization; the explicit `public` modifier and interface lock, not the namespace spelling, determine whether they are public. Their publication is justified by the mathematical statements in this Blueprint as well as downstream use. Local proof steps remain private. No alias parser adapter or manual proof-state override is used.

## Authoring and provenance

- `blueprint/content.tex` and `blueprint/chapters/` define the eight-chapter reading order.
- `blueprint/semantic/`, including `semantic/further/`, contains ordinary mathematical definitions and results. Titles, statements and bindings are independent of proof completion or consumer patterns. Historical `frontier:...` labels remain stable reading references and carry no grouping semantics.
- `blueprint/paper/` contains original AimPaper statements with source locators, citations and scope explanations. A single permanence node retains the aliases for Theorems 1.4 and 7.1. Original source material remains available under `AimPaper/`. Paper metadata is used for source links and diagram rendering, not to impose dependency-review or correspondence-registration requirements.
- All authored entries may use native statement and proof dependencies. A mathematical prerequisite need not consume every Lean declaration bound to its target.
- `% Blueprint note:` and `% Correspondence:` explanations are published as ordinary native node comments. The note adapter preserves human comments and does not add bindings, dependency edges or proof states.
- Paper commutative diagrams are rendered directly from their original TeX; a presentation copy retains lists, primes, citations and source links. This conversion does not alter bindings or dependencies. It does not modify the pinned hgraph implementation or frontend.

`corrections.yaml` remains the sole authored record of corrections relative to AimPaper. The native AimPaper corrections tab renders that record and reads revised statements from the native project payload. Scope notes and unfinished mathematical bridges remain in the Lean sources, the registry and the authored explanations. Reading links do not create mathematical dependencies or claim proof completion. See [the correction authoring guide](../docs/corrections.md).

The native **接口提案** tab presents independent agent interface reports from tracked `interface-proposals/<module>/<id>/report.md` files. It supports full-report search, module/status filters, report downloads and review feedback for agents to write back to the same record. Existing archived reports retain their original approval scope and evidence limits. Export does not require the local archive or change formal interfaces, mathematical dependencies or proof states. See [the proposal guide](../docs/interface-proposals.md).

Generated hgraph nodes, edges, web presentation copies and `_site/` are reproducible outputs. Existing native comments and reviews remain attached to their nodes. Historical compiler evidence and retired graph-import material belong under ignored `local-history/`, not in the active export pipeline. The old implementation-index and verification web pages remain retired.

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
