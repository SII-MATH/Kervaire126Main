---
author: blueprint-authoring
authored_source: blueprint/chapters/AdamsComputation.tex
blueprint_label: sem:E2Computation:two-line-exhaustive
created: '2026-10-18T04:35:45'
date: '2026-10-18T04:35:45'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.581020+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Original source checked directly: [Adams60](https://doi.org/10.2307/1970147), Theorem 2.5.1(2), pp.~44--45, gives the second-line basis h_j h_i for j>=i>=0 and j!=i+1. [LinExt4](https://doi.org/10.1016/j.topol.2007.11.003), Theorem 1.2, p.~460, recalls this earlier result and is not its original source. Distinct ordered power-of-two pairs have distinct sums, so each nonzero homogeneous element over F2 is a single basis product. The theorem is adapted to integer grading, actual page products and their degree transports. Identification of the abstract Ext basis with the project's fixed E2 product remains the registered AdamsComputation obligation; this source check does not prove it. The finite archive bound t<=261 is not extrapolated. Primary text: [Adams](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Adams-HI1.pdf), Theorem 2.5.1(2), p.45.