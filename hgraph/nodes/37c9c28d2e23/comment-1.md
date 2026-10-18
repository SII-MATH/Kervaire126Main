---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.16
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T14:34:09.108490+00:00'
---
Mathematical dependency review: [AimPaper source, lines 593-595](paper/main.tex.html#L593). Specialize Corollary 2.15 to an identity lower horizontal map.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L576; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.extensionTriangle`. The public statement is proved without changing its type or premises.

The common-source representative criterion proves the third extension directly. The conclusion keeps length $m-n$, including the signed-length cases of the fixed statement.