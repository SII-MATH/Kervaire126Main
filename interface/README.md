# Interfaces

This directory is the canonical source for the native hgraph **Interfaces** tab.

- `baselines/`: the eight public API locks, the permitted proof-obligation and audit-boundary registry, and the reviewed identifier-rename list. Lean builds validate these files; website export only presents them.
- `proposals/<module>/<id>/report.md`: interface review reports and human decisions, with optional evidence beside each report. These records feed the **Proposals** section.
- `proposals/TEMPLATE.md`: the report template used by the proposal command.

Use [the baseline guide](../docs/metadata-baselines.md) for checks and authorized updates, and [the proposal guide](../docs/interface-proposals.md) for submission and review. Run `scripts/build-blueprint.py` through the pinned Blueprint environment to refresh both sections.

The former root directories `metadata/` and `interface-proposals/` have been consolidated here. Baseline, report and evidence contents were preserved during the move. Old paths and hashes inside historical reports, evidence and `local-history/` continue to describe their original review snapshots; use this directory for current operations. No mathematical declaration, interface type, approval scope or proof permission changes with this layout.
