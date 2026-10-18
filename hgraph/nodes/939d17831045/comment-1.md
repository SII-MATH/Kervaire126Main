---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.7
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:16:05.568103+00:00'
---
Mathematical dependency review: [AimPaper source, lines 344-352](paper/main.tex.html#L344). A crossing is a competing extension from a higher-filtration source, using the extension relation already defined.

The generic filtered-map crossing predicate belongs to \ref{sem:SpectralSequence:crossing-transport}. The bindings here are the two stated no-crossing predicates with an arbitrary filtration threshold.

**Formal scope:** partial.

Public representative-level definitions `FilteredNoCrossingRange` and `ExtensionNoCrossingRange` allow arbitrary filtration thresholds. Their comparison with `DifferentialDatum` and `HasCrossingAt` for a general classical $f$-extension spectral sequence has not yet been assembled into a complete public bridge, so this correspondence remains partial.

Direct formal counterparts: `KIP126.ProofTools.Paper.FilteredNoCrossingRange`, `KIP126.ProofTools.Paper.ExtensionNoCrossingRange`.

Original statement and context: paper/main.tex.html#L344; paper/2412.10879.pdf.