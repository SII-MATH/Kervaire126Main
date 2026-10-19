---
author: blueprint-authoring
authored_source: blueprint/semantic/Literature.tex
blueprint_label: sem:Literature:one-line-differentials
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T07:58:21.573265+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. The target is the actual product h0 h_(j-1)^2, not a separate arbitrary class. For j>=4 the Nat expression j-1+1 equals j, so the Lean target degree is (3,1+2^j). This verifies the mathematical source and the stated adaptation, not the pending comparison with the fixed project model. No Lean proof obligation is discharged by this audit. Primary references: [Adams58](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Adams-SS.pdf): Lemma 2.3 and the following m=0 paragraph; pages 184 [LWX126](https://arxiv.org/abs/2412.10879): Introduction, unnumbered displayed Hopf-invariant-one differential; pages 2

Detailed source attribution: (From [Adams58](https://doi.org/10.1007/BF02564578), Lemma 2.3, p.~184; and [LWX126](https://arxiv.org/abs/2412.10879), Introduction, p.~2, the displayed Hopf-invariant-one differential.)