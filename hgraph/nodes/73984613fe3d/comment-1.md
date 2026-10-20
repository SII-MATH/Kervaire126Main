---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: paper:2.12
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.943759+00:00'
---
Mathematical dependency review: [AimPaper source, lines 483-505](paper/main.tex.html#L483). Use the representative criterion to choose a common source and transport its images around the commutative square.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L461; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.extensionSquare`. The public statement is proved without changing its type or premises.

The proved finite-filtration representative criterion synchronizes the two source edges. The zero $q$-extension puts the same representative above $s+n+k$; only the stated threshold no-crossing condition for $g$ is then used.