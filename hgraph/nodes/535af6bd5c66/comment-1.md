---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: sem:Literature:tmf-d-three
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.806226+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

BR21, Theorem 5.18 and Table 5.4, writes the target as $\beta g^4$; Table 3.5 gives $\beta^4=g^3$, so this equals the AimPaper expression $\beta^5g$. Identifying the specified formal target with this source label remains an external-input obligation.

Source verification (2026-10-18): Source adaptation checked. The cited papers concern the usual classical spectrum or its 2-primary/2-completed version. Recognition of the fixed project category, Adams tower, coefficient object, and selected Lean constants is a separate, currently pending formal comparison; this audit does not prove it. Primary references: [BR21](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rognes-bruner-tmf-book.pdf): BR21 Theorem5.18;Table5.4,p196;Remark5.9,p190;Table3.5,p151;Theorem1.20 proof,p77; AimPaper Appendix,paragraph immediately beforeTable5; Theorem5.18;Table5.4,p196;Proposition5.8(4)andRemark5.9,p190;Table3.5,p151;Table1.3,p65; Source differential:Theorem5.18andTable5.4,p196;projectderivation:Standard.lean:510–514; BR21 Proposition1.12;Table1.3,p65,restrictionw2↦v2^8;Table5.4,p196,roww2²; AimPaper Appendix,paragraph immediately beforeTable5: d3(v2^16)=β^5g; Author preliminary version of AMS Mathematical Surveys and Monographs 253 (2021), downloaded 2026-10-18; printed page numbers cited, PDF index = printed page + 17 in the body. [LWX126](https://arxiv.org/abs/2412.10879): BR21 Theorem5.18;Table5.4,p196;Remark5.9,p190;Table3.5,p151;Theorem1.20 proof,p77; AimPaper Appendix,paragraph immediately beforeTable5; BR21 Proposition1.12;Table1.3,p65,restrictionw2↦v2^8;Table5.4,p196,roww2²; AimPaper Appendix,paragraph immediately beforeTable5: d3(v2^16)=β^5g; Repository AimPaper/main.tex and2412.10879.pdf, frozen baseline. Used only as secondary notation/recall; original BR21 and BMQ checked independently.

Detailed source attribution: (A detector-transport revision of [BR21](https://doi.org/10.1090/surv/253), Theorem 5.18 and Table 5.4, using $\beta^4=g^3$ from Table 3.5; detector transport is a project construction.)