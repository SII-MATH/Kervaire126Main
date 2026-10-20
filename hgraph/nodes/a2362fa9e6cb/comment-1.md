---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: sem:Literature:infinite-finite-window
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.821401+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. BHS Corollary A.9 gives the untruncated E-infinity subquotient, and Corollary A.11 gives the finite quotient. All formula indices transform by s-omega=t-w. The finite formula holds for q>=1 in BHS, while AimPaper Proposition 3.12 explicitly states q>=2. Additive equivalences are viewed as Z-linear without a change of scalar structure. Matching a specific E2 representative to its quotient class requires the canonical label-compatible presentation, not an arbitrary abstract isomorphism. Zero labels are permitted in subgroup and quotient statements. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [BHS](https://arxiv.org/pdf/1910.14116v3): Corollary A.11(1)-(3) and its proof; Notation A.10; pages arXiv PDF p. 73; published p. 308; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344 [LWX126](https://arxiv.org/html/2412.10879v2#S3): Proposition 3.12; pages local PDF p. 17; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked [LWX126](https://arxiv.org/html/2412.10879v2#S3): Remark 3.14; pages local PDF p. 17; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked

Detailed source attribution: (From [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Corollary A.11, and [LWX126](https://arxiv.org/abs/2412.10879), Proposition 3.12 and Remark 3.14.)