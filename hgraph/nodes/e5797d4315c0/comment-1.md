---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: sem:Literature:first-quotient-products
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.848676+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. Symmetric monoidality gives multiplicativity of the canonical Ext comparison, with s,t,s-prime,t-prime nonnegative and stem t-s. Identification with the project’s selected firstQuotient and sphereAlgebra product is still an explicit pending comparison. This packages the already selected sphere first-quotient equivalence; its external origin is the source Ext comparison, while this exact additive equivalence is project data. The Lean proof composes quotientAlgebra_sphere_action with quotientAlgebra_first_quotient. It is not a further external theorem or a completed upstream comparison. Primary references: [Pst](https://arxiv.org/pdf/1803.01804v3): Corollary 4.30; Theorem 4.46; Lemma 4.56; pages 46, 50–51, 54; arXiv:1803.01804v3, 10 November 2022

Detailed source attribution: (From [Pst](https://doi.org/10.1007/s00222-022-01173-2), Theorem 4.46 and Lemma 4.56, using the first-quotient algebra of Corollary 4.30.)