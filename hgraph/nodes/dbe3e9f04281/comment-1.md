---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:differential-rigidity
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T04:35:45.805562+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. Tau is renamed lambda, the third grading is changed as specified in Remark 3.7, and the formula is extended by lambda-linearity and the shift (0,a). The displayed source and target both have weight t+a-k. The Lean relation HasDifferential requires representatives of both E_2 labels on E_r; it permits a zero target. The mathematical source has been checked; identification with the project's specified coefficient object, Adams towers, quotient maps and realization remains part of the existing formal comparison obligations. No Lean proof obligation is discharged by this citation. Primary references: [BHS](https://arxiv.org/pdf/1910.14116v3): Theorem A.8(2)–(3); pages PDF p. 72; arXiv:1910.14116v3, 10 May 2022; final prepublication version, not published pagination [LWX126](https://arxiv.org/abs/2412.10879): Theorem 3.6 and Remark 3.7; pages PDF p. 16; Repository AimPaper/main.tex and AimPaper/2412.10879.pdf; exact local source snapshot

Detailed source attribution: (Adapted from [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Theorem A.8(3); [LWX126](https://arxiv.org/abs/2412.10879), Theorem 3.6 and Remark 3.7.)