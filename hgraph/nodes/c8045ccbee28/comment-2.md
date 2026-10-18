---
author: blueprint-authoring
authored_source: blueprint/paper/Main.tex
blueprint_label: paper:7.9
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T14:03:28.770545+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Original proof: [AimPaper source, lines 2698-2778](paper/main.tex.html#L2698), using Lemma 7.16 and Corollary 7.18 before the nu extension and cofiber contradiction. The retained formal route is explained at sem:Main:weak-representative-route: it preserves the nonzero lambda-squared h0 value while removing low-filtration terms and does not invoke either pending public statement. The authored dependencies follow this retained route; the original statements and their unresolved proof obligations remain separately visible.

**Formal scope:** Public correspondence.

The public theorem proves that vanishing of the specified sixth differential excludes the specified eta-extension detection, with no additional caller premise. Its locally completed proof inherits registered upstream obligations.

Formal counterparts: `KIP126.Main.eta\_extension\_excluded\_of\_d6\_vanishes`.

Original statement: paper/main.tex.html#L2208; article PDF: paper/2412.10879.pdf.