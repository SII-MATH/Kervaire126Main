---
author: blueprint-authoring
authored_source: blueprint/paper/SpectralSequence.tex
blueprint_label: paper:2.1
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T07:48:14.566506+00:00'
---
Mathematical dependency review: [AimPaper source, lines 253-271](paper/main.tex.html#L253). Filter the two-term complex by Adams filtration to form the extension spectral sequence.

The direct binding is the bounded extension spectral sequence construction. The separate theorem identifying its differentials with extension equations is stated in \ref{sem:SpectralSequence:ess-equation}.

**Formal scope:** partial.

The extension spectral sequence of the same filtered map is constructed under `IsBounded` hypotheses on the source and target filtrations. A dedicated construction for an arbitrary classical map $f$, together with the full abutment comparison in the paper, is not yet supplied.

Direct formal counterparts: `KIP126.Core.SpectralSequence.FilteredMapExtension.sequence`.

Original statement and context: paper/main.tex.html#L264; paper/2412.10879.pdf.