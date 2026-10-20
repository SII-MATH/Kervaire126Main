---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: paper:3.17
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T03:59:04.670059+00:00'
---
Mathematical dependency review: [AimPaper source, lines 929-940](paper/main.tex.html#L929). Apply synthetic cofiber preservation to the homology-exact triangle and use the suspension comparison for its boundary; the proof is in BHS Lemma 9.15.

**Formal scope:** public correspondence with the scope stated below

Positive filtration and the full homology short exactness are retained. The factorization concerns the same connecting arrow and distinguished triangle; comparison of arbitrary full lifts is only modulo lambda torsion.

Direct formal counterparts: `KIP126.Literature.Standard.triangle\_lift`.

Source verification (2026-10-18): Original source text. The interface existentially chooses a connecting arrow and its distinguished triangle under positive filtration and homology exactness; its full-lift comparison is only modulo lambda torsion, as in AimPaper Remark 3.18. Primary references: [BHS](https://arxiv.org/pdf/1910.14116v3): Lemma 9.15 and its proof; pages 34–35; arXiv:1910.14116v3, 10 May 2022 [LWX126](https://arxiv.org/abs/2412.10879): Propositions 3.16–3.17; Remark 3.18; pages 18–19; Repository-frozen AimPaper/main.tex and AimPaper/2412.10879.pdf

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Proposition 3.17; see the proof of [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1), Lemma 9.15, and [LWX126](https://arxiv.org/abs/2412.10879), Remark 3.18.)