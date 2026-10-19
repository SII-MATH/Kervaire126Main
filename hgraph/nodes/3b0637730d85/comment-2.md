---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:lambda-inversion
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T07:58:21.584306+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. The chosen SSDataMorphism includes all cycle and boundary levels, including the project infinity construction; this is packaging beyond the literal printed spectral-sequence morphism. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [Pst](https://arxiv.org/pdf/1803.01804v3): Proposition 4.36; Theorem 4.37; Proposition 4.40; pages arXiv PDF pp. 47-49; published pp. 621-624; arXiv:1803.01804v3, 10 November 2022; numbering also checked in Invent. Math. 232 (2023) [BHS](https://arxiv.org/pdf/1910.14116v3): paragraph immediately before Notation A.7; proof of Theorem A.8; pages arXiv PDF p. 72; published p. 307; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344 [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.8; Notation A.6; pages arXiv PDF pp. 71-72; published pp. 306-307; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344

Detailed source attribution: (From [Pst](https://doi.org/10.1007/s00222-022-01173-2), Proposition 4.40, and [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Notation A.6, the comparison before Notation A.7, and Theorem A.8.)