---
author: blueprint-authoring
authored_source: blueprint/paper/Main.tex
blueprint_label: paper:7.18
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T07:48:14.540657+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 2577-2584](paper/main.tex.html#L2577). Read the h0 multiple from the bracket proof and absorb the higher-filtration correction into the chosen target representative; the same ambiguity argument handles every source representative.

A goal predicate and a theorem restricted to Toda-bracket members do not establish the quantified assertion for every detected representative. No direct formal counterpart is bound here.

**Formal scope:** Partial correspondence.

The predicate AnyYH0Extension states the full goal for every detected representative. A private theorem proves the exact nonzero $h_0$ equation for members of the same Toda bracket. The predicate is not a proof; annihilation of the difference between an arbitrary detected $Y$ representative and such a bracket member is still missing.

Original statement: paper/main.tex.html#L2571; article PDF: paper/2412.10879.pdf.