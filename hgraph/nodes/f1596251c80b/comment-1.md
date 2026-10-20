---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: paper:3.6
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.662500+00:00'
---
Mathematical dependency review: [AimPaper source, lines 799-807](paper/main.tex.html#L799). BHS supplies the polynomial-lambda Adams page and its differential rule for the synthetic analogue.

**Formal scope:** public correspondence with the scope stated below

The public statements separate page coordinates, the free-lambda range, and differential rigidity. Their object scope is the project ClassicalObject closure; it is not a claim about every arbitrary external spectrum.

Direct formal counterparts: `KIP126.Literature.Standard.nuPage\_e2`, `KIP126.Literature.Standard.bhs\_differentials`.

Source verification (2026-10-18): Original source text. From refers to the immutable AimPaper body, not to a claim that all clauses are already covered by the selected Lean bindings. Bound free comparison statements cover part of the full rigidity theorem, with their existing proof obligations. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [LWX126](https://arxiv.org/html/2412.10879v2#S3): Theorem 3.6 and Remark 3.7; pages local PDF p. 16; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.8; Notation A.6; pages arXiv PDF pp. 71-72; published pp. 306-307; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.6; adapted there from [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.8, with the regrading in Remark 3.7.)