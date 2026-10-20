---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: paper:3.8
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T05:53:20.592357+00:00'
---
Mathematical dependency review: [AimPaper source, lines 813-823](paper/main.tex.html#L813). BHS identifies the Adams and lambda-Bockstein sequences, including lifts and the connecting differential. It is a separate external input, not a consequence asserted from Theorem 3.6 alone.

**Formal scope:** public correspondence with the scope stated below

The public correspondence uses the actual first quotient and classical labels, finite lifts, and Bockstein differentials, retaining the selected objects and comparison conditions.

\item `KIP126.Literature.Standard.bhs\_finite\_lift`

\item `KIP126.Literature.Standard.bhs\_bockstein`

\item `KIP126.Literature.Standard.bhs\_differentials`

Source verification (2026-10-18): Original source text. Do not alter the original occurrence of tau-Bockstein in the AimPaper raw block. The source attribution should not silently strengthen the chosen Lean bindings into a proof of the complete spectral-sequence isomorphism. Theorem A.1 has E-nilpotent completeness and strong-convergence hypotheses; finite-page information is proved earlier under weaker hypotheses, while untruncated homotopy applications retain the full hypotheses. Write the BHS coordinates as (s,k,omega) and the project coordinates as (s,t,w). The translation is k=t-s and omega=w-(t-s); tau is renamed lambda. Hence s-omega=t-w, and the BHS differential degree (r,-1,1) becomes (r,r-1,0). This verifies the mathematical source and its stated regrading, not the outstanding Lean comparison with the fixed project model. Existing Lean proof and transitive-dependency status must remain unchanged. Spectral-sequence page and E-infinity subquotient statements here do not assert convergence to untruncated homotopy groups; BHS Convention A.5 allows an arbitrary spectrum for Theorem A.8 and Corollaries A.9/A.11. Primary references: [LWX126](https://arxiv.org/html/2412.10879v2#S3): Theorem 3.8; pages local PDF p. 16; arXiv:2412.10879v2, 22 February 2025; local AimPaper/main.tex and PDF also checked [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.1(1); Theorem A.8; proof of Proposition A.16; pages arXiv PDF pp. 70-72,75-76; published pp. 304-307,311-312; arXiv:1910.14116v3, 10 May 2022; checked against Acta Math. 231 (2023), 205-344

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.8; see [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.1(1), Theorem A.8 and the Bockstein reindexing in the proof of Proposition A.16.)

Source verification (2026-10-18): Source adaptation checked. Finite-quotient result: write q for BHS r, identify tau with lambda, and use stem k=t-s. Reaching E_(q+1) means d_2 through d_q vanish; zero and earlier boundaries are allowed. Unlike the untruncated conclusion, the finite case extends to arbitrary spectra via Corollary A.11 and Lemma A.14, as in the proof of Theorem A.1(1). Over F_2 the sign in A.1(1c) disappears. The mathematical source has been checked; identification with the project's specified coefficient object, Adams towers, quotient maps and realization remains part of the existing formal comparison obligations. No Lean proof obligation is discharged by this citation. Primary references: [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.1(1a)–(1c); Corollary A.11; Lemma A.14; proof of Theorem 9.19(1); pages PDF pp. 70, 73–75; arXiv:1910.14116v3, 10 May 2022; final prepublication version, not published pagination [LWX126](https://arxiv.org/abs/2412.10879): Theorem 3.8(1)–(2); pages PDF p. 16; Repository AimPaper/main.tex and AimPaper/2412.10879.pdf; exact local source snapshot

Detailed source attribution: (From [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.1(1a)--(1b), Corollary A.11 and Lemma A.14; [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.8.)

Detailed source attribution: (A selected-model revision of [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.1(1c) and its proof, Corollary A.11 and Lemma A.14; [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.8(2).)