---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: paper:2.17
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.863089+00:00'
---
Mathematical dependency review: [AimPaper source, lines 613-615](paper/main.tex.html#L613). Specialize Corollary 2.15 to an identity upper horizontal map.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L597; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.extensionComposition`. The public statement is proved without changing its type or premises.

The printed occurrence of $Y$ for $z$ is read as $Z$, as forced by the diagram; the unused $n$ and the printed $n,m\ge0$ are retained without adding $l\ge0$. See the statement-typing correction record.

Apply the lower no-crossing criterion to the actual image of a source representative, then use the composite equality. No additional condition $l\ge0$ is imposed.