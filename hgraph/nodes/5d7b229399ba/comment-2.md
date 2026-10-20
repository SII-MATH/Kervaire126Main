---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: sem:Literature:connected-homology
created: '2026-10-17T18:17:09'
date: '2026-10-17T18:17:09'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T05:44:00.421051+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

Source verification (2026-10-18): Source adaptation checked. The notation H^n here means the project legacy group [Sigma^n X,HF2], i.e. ordinary H^{-n}. The connectivity definition and this sign convention are project definitions. The UCF uses the full dual and requires no finite-type assumption. This verifies the mathematical source and the stated adaptation, not the pending comparison with the fixed project model. No Lean proof obligation is discharged by this audit. Primary references: [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf): Example I.1.8; proof of Proposition II.5.21; pages [12, 264] [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf): Proposition II.5.22; Example I.1.14; Definition II.6.21; pages [16, 17, 264, 265, 278, 279] [EKMM](https://www.math.uchicago.edu/~may/BOOKS/EKMM.pdf): Proposition IV.1.2(i), after shifting X by -(n+1); pages [72] [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf): Proposition II.6.28 and Equation (6.27); pages [281] [EKMM](https://www.math.uchicago.edu/~may/BOOKS/EKMM.pdf): Theorem IV.4.5, specialized R=N=HF2; pages [82]

Detailed source attribution: (From [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf), Example I.1.8, Proposition II.5.22, and Definition II.6.21; and from [EKMM](https://www.math.uchicago.edu/~may/BOOKS/EKMM.pdf), Theorem IV.4.5, specialized to $H\mathbb F_2$. The cohomological degree uses the project convention $H^n_{\mathrm{legacy}}(X)=H^{-n}(X;\mathbb F_2)$.)

Source verification (2026-10-18): Source adaptation checked. The displayed H^n is legacy [Sigma^n X,HF2], equivalent to ordinary H^{-n}. There is no finite-dimensional or finite-type restriction. Hom_Ab coincides with F2-linear Hom because the only scalars are zero and one. This verifies the mathematical source and the stated adaptation, not the pending comparison with the fixed project model. No Lean proof obligation is discharged by this audit. Primary references: [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf): Proposition II.6.28 and Equation (6.27); pages [281] [EKMM](https://www.math.uchicago.edu/~may/BOOKS/EKMM.pdf): Theorem IV.4.5, specialized R=N=HF2; pages [82]

Detailed source attribution: (From [EKMM](https://www.math.uchicago.edu/~may/BOOKS/EKMM.pdf), Theorem IV.4.5, specialized to $H\mathbb F_2$; equivalently [SchwedeSymmetricSpectra](https://www.math.uni-bonn.de/~schwede/SymSpec-v3.pdf), Proposition II.6.28 and Equation (6.27), with the project indexing $q=-n$.)