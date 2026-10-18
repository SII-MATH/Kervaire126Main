---
author: blueprint-authoring
authored_source: blueprint/paper/Literature.tex
blueprint_label: paper:3.16
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T04:35:45.861796+00:00'
---
**Formal scope:** public correspondence with the scope stated below

The same classical map and an actual tower-filtration bound give the factorization through a lambda power.

\item `KIP126.Literature.Standard.lift`: [implementation](implementation/index.html#decl:f5227c15ec1381e8)

\item `KIP126.Literature.SyntheticFullLift`: [implementation](implementation/index.html#decl:1d3eeae5375e6c50)

\item `KIP126.Literature.SyntheticLiftComparison`: [implementation](implementation/index.html#decl:94c09dff696f6394)

Source verification (2026-10-18): Original source text. The displayed raw AimPaper statement is unchanged. The bound Lean SyntheticFullLift uses the same negative-target convention. SyntheticLiftComparison accepts filtration at least k, a natural bound version obtained from k successive filtration-one factorizations (including k=0). It remains an admitted comparison for the fixed project tower. The mathematical source has been checked; identification with the project's specified coefficient object, Adams towers, quotient maps and realization remains part of the existing formal comparison obligations. No Lean proof obligation is discharged by this citation. Primary references: [LWX126](https://arxiv.org/abs/2412.10879): Proposition 3.16; pages PDF pp. 18–19; main.tex lines 912–927; Repository AimPaper/main.tex and AimPaper/2412.10879.pdf; exact local source snapshot [BHS](https://arxiv.org/pdf/1910.14116v3): Lemma 9.15 and its proof; pages PDF pp. 34–35; arXiv:1910.14116v3, 10 May 2022; final prepublication version, not published pagination

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Proposition 3.16; see [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Lemma 9.15.)