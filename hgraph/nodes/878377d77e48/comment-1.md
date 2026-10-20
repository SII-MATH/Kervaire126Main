---
author: blueprint-authoring
authored_source: blueprint/chapters/AdamsSynthetic.tex
blueprint_label: paper:2.5
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.761303+00:00'
---
Mathematical dependency review: [AimPaper source, lines 307-325](paper/main.tex.html#L307). Representatives detected by x and y characterize extensions; the indeterminacy statements follow from the same characterization.

This entry binds the representative-existence equivalence for a convergent synthetic map. The independent generic coset and higher-filtration conclusions belong to \ref{sem:SpectralSequence:extension-coset} and \ref{sem:SpectralSequence:higher-filtration}; they are not additional bindings of this statement.

**Formal scope:** partial.

Public components cover the existence of representatives, target indeterminacy at a fixed length, and higher-filtration corrections. No public theorem covering all clauses of the paper statement has been identified, in particular the $m>n$ branch and the essential shorter-differential witness.

Direct formal counterparts: `KIP126.AdamsSynthetic.ConvergentMap.extensionEquation\_iff`.

Original statement and context: paper/main.tex.html#L307; paper/2412.10879.pdf.