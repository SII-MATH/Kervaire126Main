---
author: blueprint-authoring
authored_source: blueprint/chapters/Main.tex
blueprint_label: paper:7.18
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.788690+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 2577-2584](paper/main.tex.html#L2577). Read the h0 multiple from the bracket proof and absorb the higher-filtration correction into the chosen target representative; the same ambiguity argument handles every source representative.

The public theorem states the complete assertion for every detected source representative, with a target representative depending on that source. Its proof now applies the independently established incompatibility of the two explicit hypotheses. The complete universal statement and exact unmultiplied equation are unchanged; this proof does not infer the equation merely from higher filtration or cancel a lambda factor.

**Formal scope:** Complete conditional statement, proved by the independent exclusion of its hypotheses.

The predicate AnyYH0Extension states the full goal for every detected representative. Private proofs establish the exact nonzero $h_0$ equation for members of the same Toda bracket, choice independence of $\lambda^2h_0y$ for all $Y$-detected representatives, and choice independence of $\lambda^6t$ for all $T$-detected representatives. The direct representative-error argument for the unmultiplied assertion remains unfinished: higher filtration alone does not make an $h_0$ error vanish or allow it to be absorbed by changing $t$. A separately checked finite-quotient construction produces an actual filtration-15 error with nonzero $h_0$ image; it does not supply a counterexample satisfying all hypotheses of this corollary. A new private equivalence makes the remaining condition exact: given an initial nonzero equation $h_0y_0=\lambda^6t_0$, a specified representative $y$ admits the required target if and only if $h_0(y-y_0)=0$. The same equivalence holds with the original universal quantifier over all $Y$-detected representatives. It adds no premise to the public corollary. The completed conditional proof instead excludes the two original hypotheses by the independent Proposition 7.9 route.

Original statement: paper/main.tex.html#L2571; article PDF: paper/2412.10879.pdf.