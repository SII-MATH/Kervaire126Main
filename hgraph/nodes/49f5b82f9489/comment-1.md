---
author: blueprint-authoring
authored_source: blueprint/chapters/AdamsCalculations.tex
blueprint_label: sem:AdamsCalculations:two-line-d2-screening
created: '2026-10-18T04:35:45'
date: '2026-10-18T04:35:45'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.729665+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Detailed original sources: [Adams58](https://doi.org/10.1007/BF02564578), Theorem 2.2(iii), p.~182, supplies multiplicative Leibniz. [Adams60](https://doi.org/10.2307/1970147), Theorem 4.6.1, pp.~99--100, supplies the secondary-operation relation whose Adams interpretation is d2(h_j)=h0 h_(j-1)^2 for j>=4; the modern d2 formula is an adaptation, not a verbatim statement of that theorem. [LinExt4](https://doi.org/10.1016/j.topol.2007.11.003), Theorems 1.2--1.3, pp.~460--461, supplies the products and relations on the first four lines. These are the primary ingredients for a derived calculation, not a literal theorem of Lin.

Independent source audit found (0,4) to be a counterexample to the earlier candidate list. The product is nonzero by [Adams60](https://doi.org/10.2307/1970147), Theorem 2.5.1(2), p.~45. Lin Theorem 1.3(1), at i=0, gives h0^2 h3^2=0, hence Leibniz gives d2(h0 h4)=0. Its later nonzero d3 is explicit in [IWX](https://doi.org/10.1007/s10240-023-00139-1), Table 6, p.~222. The user approved the correction: add (0,4), supply its separate nonzero d3 Literature interface, and add its exclusion branch in Main. The final permanent-survivor statement is unchanged, and the one additional upstream responsibility raises the total from 309 to 310. The corrected screening and source-to-fixed-model comparison remain a registered upstream proof obligation; citation verification and finite checks do not prove the unbounded interface.