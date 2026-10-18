---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:moss-convergence
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T04:35:45.820780+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Moss's crossing convention differs from the paper's extension-crossing convention.

Source verification (2026-10-18): Source adaptation checked. Moss Theorem 1.2 assumes weak convergence of all five input/product Adams systems, not only the two product systems. For this fixed sphere mapping family, the separately bound global moss_weak_convergence statement supplies all five; the displayed StatementAt lists only the two product-tower premises. For each product degree u, put n=q in source condition (1.3): 0<=q<=u_1-r becomes 0<=q<u_1-(r-1), and an outgoing page m satisfies u_1<q+m (hence m>r). The source model is Boardman stable homotopy with Adams systems for a cohomology functor. Identification of the chosen project mapping system, the shifted stable maps and sign conventions remains a comparison obligation; this is not a theorem about arbitrary triangulated categories. Primary references: [Moss](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0115/LOG_0047.pdf): Section 1; Theorem (1.2) and conditions (1.3); pages 283–285; Original Math. Z. 115 (1970), 283–310; GDZ digitized journal scan LOG_0047 [BelmontKong2024](https://arxiv.org/pdf/2112.08689v2): Definitions 2.3–2.4; Theorem 4.10 and Assumptions 3.14, 3.17; pages 5, 12–13, 16–17; arXiv:2112.08689v2, 16 August 2024 (not a different published numbering)

Detailed source attribution: (Adapted from [Moss](https://doi.org/10.1007/BF01129978), Theorem 1.2 and conditions (1.3), with the global weak-convergence hypothesis from Section 1.)