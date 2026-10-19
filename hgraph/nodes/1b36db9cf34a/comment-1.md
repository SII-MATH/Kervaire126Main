---
author: blueprint-authoring
authored_source: blueprint/paper/Main.tex
blueprint_label: paper:7.16
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T06:19:35.728638+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 2482-2566](paper/main.tex.html#L2482). Form the bracket using alpha-one, identify its nonzero h0 multiple, and rule out the lower-filtration candidates using the low and symmetric Toda laws, Moss convergence and the sphere computations. The assumed conditions do not invoke Proposition 7.8 as a theorem.

The public theorem states the complete nonzero detection conclusion for the same synthetic Toda bracket in the actual ninth lambda quotient. Its proof now applies the independently established incompatibility of the two explicit hypotheses, proved by the retained route for Proposition 7.9. This does not complete the original direct Toda-detection calculation. Nonemptiness and the equation after multiplication by h0 remain supporting results.

**Formal scope:** Complete conditional statement, proved by the independent exclusion of its hypotheses.

Private proofs construct the same nonempty Toda bracket in the ninth lambda quotient and the exact nonzero target after multiplication of any bracket member by $h_0$. All members have the same actual image under $Q_9\to Q_3$, and, under the stated hypotheses, detection by $\lambda^4Y$ is equivalent to that image being zero. The direct local proof of vanishing of this common image remains unfinished; the original bracket member cannot be replaced by a different high-filtration representative. The difference of any two actual bracket members is now proved to lie in $F^{11}$, and every member is nonzero. One actual $F^{11}$ bracket member would therefore establish the full universal detection conclusion. Removing low-filtration terms while preserving only $\lambda^2h_0$ does not establish membership in this same bracket. The original proof also passes from an equality of eta images to an equality before applying eta; the required kernel control has not been supplied.

Original statement: paper/main.tex.html#L2470; article PDF: paper/2412.10879.pdf.

The original argument also invokes Moss convergence. Its general mapping-spectrum framework is outside the current Main proof route and is not displayed here; the completed conditional proof does not claim that this omitted source input or the original local proof has been supplied.