---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: paper:2.19
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.866120+00:00'
---
Mathematical dependency review: [AimPaper source, lines 637-646](paper/main.tex.html#L637). The null-composite square proves permanence; the article also gives a representative proof using Proposition 2.5.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L632; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.permanentCycle\_of\_nullComposite`. The public statement is proved without changing its type or premises.

The original extension supplies a single representative in the actual image of $f$. Its composite with $g$ is zero, so that same representative witnesses every zero outgoing extension.