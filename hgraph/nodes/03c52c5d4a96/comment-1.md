---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:toda-functoriality
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T07:58:21.623694+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. Pre/postcomposition and absorption are containments, not equality of arbitrary brackets. Juggling/shuffle additionally assume the octahedral axiom and retain the shifted negative sign. Suspension retains (-1)^n and actual shift comparisons. Exact-functor and tensor claims require CommShift and IsTriangulated for the same functor; their proofs transport the complete cofiber witness and claim containment only. Primary references: [ChristensenFrankland2017](https://arxiv.org/pdf/1510.09216v3): Definition 3.1, Lemmas 3.4–3.5 and 5.12; pages 8, 11, 21; arXiv:1510.09216v3, 12 August 2017; closely matches AGT 17 (2017), 2687–2735 [LWX126](https://arxiv.org/abs/2412.10879): Theorem 7.3, Remarks 7.4–7.5; Example 5.8(4); proof of Lemma 7.16; pages 42, 28, 49–50; Repository AimPaper/main.tex and AimPaper/2412.10879.pdf snapshot; no unstated version substitution

Detailed source attribution: (From [ChristensenFrankland2017](https://arxiv.org/abs/1510.09216v3), Definition 3.1 and Lemmas 3.5 and 5.12; the exact-functor and tensor transport laws are derived here.)