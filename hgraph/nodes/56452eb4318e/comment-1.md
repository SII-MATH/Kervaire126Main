---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:nu-page-coordinates
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T07:58:21.581866+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. The public shift isomorphism includes integer pages below 2; those pages are frozen to the first page by a project convention, not covered as extra pages in the cited paper. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [Pst](https://arxiv.org/pdf/1803.01804v3): Definition 4.6; Definition 4.27; pages arXiv PDF pp. 39, 45; published pp. 609, 618; arXiv:1803.01804v3, 10 November 2022; numbering also checked in Invent. Math. 232 (2023) [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.8; Notation A.6; pages arXiv PDF pp. 71-72; published pp. 306-307; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344 [LWX126](https://arxiv.org/html/2412.10879v2#S3): Theorem 3.6 and Remark 3.7; pages local PDF p. 16; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked

Detailed source attribution: (From [Pst](https://doi.org/10.1007/s00222-022-01173-2), Definitions 4.6 and 4.27, and [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.8; grading as in [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.6 and Remark 3.7.)