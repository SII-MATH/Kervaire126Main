---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.18
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T14:34:09.110767+00:00'
---
Mathematical dependency review: [AimPaper source, lines 628-630](paper/main.tex.html#L628). Apply the square corollary inductively to obtain commuting maps on every page of the extension spectral sequences.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L617; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.extensionSpectralSequenceMorphism`. The public statement is proved without changing its type or premises.

Finite induction on the preceding vanishing extension relations proves a filtration shift by $r$. The unique degree-$r$ extension values form additive maps whose exact graphs are the $p$- and $q$-relations; the same homotopy representative and square preserve every $f$-extension relation. This proves the fixed statement in its full representative presentation; the separate construction of a classical ESS remains scoped in Definition 2.1.