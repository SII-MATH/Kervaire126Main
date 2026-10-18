---
author: blueprint-authoring
authored_source: blueprint/paper/Literature.tex
blueprint_label: paper:3.12
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T07:48:14.526750+00:00'
---
Mathematical dependency review: [AimPaper source, lines 839-855](paper/main.tex.html#L839). The finite lambda quotient truncates the polynomial-lambda sequence and gives the BHS Corollary A.11 window.

**Formal scope:** public correspondence with the scope stated below

The finite-lambda-quotient infinite-page window and its valid range are explicit.

Direct formal counterparts: `KIP126.Literature.Standard.eInfinity\_finite`.

Source verification (2026-10-18): Original source text. BHS Corollary A.9 gives the untruncated E-infinity subquotient, and Corollary A.11 gives the finite quotient. All formula indices transform by s-omega=t-w. The finite formula holds for q>=1 in BHS, while AimPaper Proposition 3.12 explicitly states q>=2. Additive equivalences are viewed as Z-linear without a change of scalar structure. Matching a specific E2 representative to its quotient class requires the canonical label-compatible presentation, not an arbitrary abstract isomorphism. Zero labels are permitted in subgroup and quotient statements. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [LWX126](https://arxiv.org/html/2412.10879v2#S3): Proposition 3.12; pages local PDF p. 17; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked [BHS](https://arxiv.org/pdf/1910.14116v3): Corollary A.11(1)-(3) and its proof; Notation A.10; pages arXiv PDF p. 73; published p. 308; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Proposition 3.12; adapted there from [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Corollary A.11.)