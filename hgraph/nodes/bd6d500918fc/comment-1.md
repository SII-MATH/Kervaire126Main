---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.6
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T14:34:09.103760+00:00'
---
Mathematical dependency review: [AimPaper source, lines 332-339](paper/main.tex.html#L332). Factor f into positive-filtration maps, then apply Proposition 2.5(1) to rule out shorter extension differentials.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L327; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.adamsFiltrationVanishing`. The public statement is proved without changing its type or premises.

The proof lifts the map along the actual target Adams tower and proves that filtration adds under composition. Every shorter extension target has zero associated grade.