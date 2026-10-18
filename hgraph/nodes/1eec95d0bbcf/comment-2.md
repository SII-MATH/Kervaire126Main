---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:may-tensor
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T04:35:45.815835+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. These choices realize integral suspension comparisons for the existing fixed synthetic tensor; TC1–TC2, not Lemma 4.6, are the relevant framework. Compatibility of this concrete choice remains to be constructed. Colimit preservation implies exactness for the synthetic stable category; the Lean declarations require this for the exact suspension structures selected above. Packages the selected left/right shift and exactness structures. The package contains TC1–TC2-style data only; it does not itself imply TC3. Primary references: [May01](https://www.math.uchicago.edu/~may/PAPERS/AddJan01.pdf): Axioms TC1–TC2; Remark 4.2; pages 11; Author-hosted January 2001 preprint, 31 pages; numbered statements retain published numbering [Pst](https://arxiv.org/pdf/1803.01804v3): Proposition 4.2; Remark 4.5; Definition 4.6; pages 38–39; arXiv:1803.01804v3, 10 November 2022

Detailed source attribution: (Adapted from [Pst](https://doi.org/10.1007/s00222-022-01173-2), Proposition 4.2, and [May01](https://doi.org/10.1006/aima.2001.1995), Axioms TC1--TC2 and Remark 4.2.)