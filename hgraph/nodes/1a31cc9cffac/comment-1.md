---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.15
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T14:34:09.107373+00:00'
---
Mathematical dependency review: [AimPaper source, lines 555-574](paper/main.tex.html#L555). Specialize the square theorem to the full no-crossing hypothesis on the lower extension.

**Formal scope:** fixed original representative-form statement proved.

Original statement and context: paper/main.tex.html#L555; paper/2412.10879.pdf.

Original-statement interface: `KIP126.ProofTools.Paper.noCrossingExtensionSquare`. The public statement is proved without changing its type or premises.

The proved filtered-group no-crossing criterion is specialized directly to the actual classical Adams tower. It synchronizes a common source representative and the lower target, and the same commutative square gives the right extension. No synthetic-to-classical comparison or additional premise is needed.