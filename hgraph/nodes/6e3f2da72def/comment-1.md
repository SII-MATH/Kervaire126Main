---
author: blueprint-authoring
authored_source: blueprint/chapters/Main.tex
blueprint_label: paper:1.5
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.927604+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 156-161](paper/main.tex.html#L156). The exhaustive second line, Adams--Lin--Leibniz screening, classical permanence/exclusions and the new h6-square case yield the classification. Use the corrected screening including h0 h4, as recorded in the existing scope note.

**Formal scope:** Public correspondence; complete local classification proof using the corrected third-page candidate interface.

This binds a proof of the complete AdamsTwoLineClassification, not its proposition-valued definition or only its stem-126 specialization. The proof has no caller premise or local sorry. Nine new Literature source/comparison obligations, one unbounded E2 basis obligation and one Adams d2-stage calculation obligation were explicitly authorized and separately registered. These upstream gaps remain visible through compiled dependency closure; the complete formalization is not yet transitively closed.

Approved source correction (2026-10-18): The original proof's E3 list omits h0 h4, which reaches E3 before its nonzero d3; see [IWX](https://doi.org/10.1007/s10240-023-00139-1), Table 6, p.~222. The corrected public candidate predicate includes it, and Main excludes it using the separately registered Literature input iwx_h0_h4_d3. All square indices likewise remain E3 candidates until the later HHR exclusion. The original final statement above is preserved. The local assembly is complete relative to the corrected upstream interfaces; their source-to-fixed-model proofs remain pending. This does not turn a compilation check into a transitive proof-completion claim.

Original statement: paper/main.tex.html#L151; article PDF: paper/2412.10879.pdf.