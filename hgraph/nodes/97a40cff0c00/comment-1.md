---
author: blueprint-authoring
authored_source: blueprint/chapters/AdamsSynthetic.tex
blueprint_label: paper:2.3
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T05:44:00.407421+00:00'
---
Mathematical dependency review: [AimPaper source, lines 277-300](paper/main.tex.html#L277). An essential extension is defined using the differentials and boundary indeterminacy of the extension spectral sequence.

The generic filtered extension relation and its essentiality are defined in \ref{sem:SpectralSequence:extension-equation} and \ref{sem:SpectralSequence:extension-equation}. This entry binds only their specialization to the convergent synthetic map.

**Formal scope:** partial.

Public definitions of extensions and essential extensions are available. The comparison with actual extension-spectral-sequence differentials retains boundedness and projectivity hypotheses; `ConvergentMap` applies specifically to synthetic families.

Direct formal counterparts: `KIP126.AdamsSynthetic.ConvergentMap.ExtensionEquation`, `KIP126.AdamsSynthetic.ConvergentMap.EssentialExtension`.

Original statement and context: paper/main.tex.html#L297; paper/2412.10879.pdf.