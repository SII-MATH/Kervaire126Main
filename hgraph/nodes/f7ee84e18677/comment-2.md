---
author: blueprint-authoring
authored_source: blueprint/paper/Main.tex
blueprint_label: paper:7.18
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T11:19:44.121589+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 2577-2584](paper/main.tex.html#L2577). Read the h0 multiple from the bracket proof and absorb the higher-filtration correction into the chosen target representative; the same ambiguity argument handles every source representative.

The public theorem states the complete assertion for every detected source representative, with a target representative depending on that source. Its proof remains pending as an explicitly registered sorry; this binding records the formalized statement and does not claim a proof. A goal predicate and a result restricted to Toda-bracket members do not establish this quantified conclusion.

**Formal scope:** Partial correspondence: complete formal statement; proof pending.

The predicate AnyYH0Extension states the full goal for every detected representative. Private proofs establish the exact nonzero $h_0$ equation for members of the same Toda bracket, choice independence of $\lambda^2h_0y$ for all $Y$-detected representatives, and choice independence of $\lambda^6t$ for all $T$-detected representatives. The unmultiplied assertion remains unproved: higher filtration alone does not make an $h_0$ error vanish or allow it to be absorbed by changing $t$. A separately checked finite-quotient construction produces an actual filtration-15 error with nonzero $h_0$ image; it does not supply a counterexample satisfying all hypotheses of this corollary.

Original statement: paper/main.tex.html#L2571; article PDF: paper/2412.10879.pdf.