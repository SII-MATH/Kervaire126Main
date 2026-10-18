---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: convergence-and-detection
title: 'Interface scope: convergence-and-detection'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `convergence-and-detection`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Relate the actual E∞ of a supplied sequence to associated grades of a specified filtration, with natural maps and detection.

- **interface_role**: Filtration and Convergence are given structures. Detection, quotient zero tests and finite-gap consequences are defined or proved from them.

- **mathematical_strength_preserved**: Convergence contains an actual reindexing and E∞ ≅ associatedGraded; it does not silently assert boundedness, Hausdorffness, exhaustiveness or existence of a concrete model.

- **mathematical_strength_preserved**: ConvergenceMorphism ties the abutment map, its filtration compatibility and E∞ map by the actual associated-graded square.

- **mathematical_strength_preserved**: detect_zero and the ModuleCat quotient-zero criterion yield an actual lift or membership in the next filtration level.

- **mathematical_strength_preserved**: Finite interval grade vanishing gives equality of its filtration endpoints without an infinite-tail separation assumption.

- **mathematical_strength_preserved**: Degreewise upper/lower bounds remain explicit data; IsHausdorff is the intersection-zero universal property, not finite-stage vanishing.

- **boundary**: Concrete tower convergence and any infinite-tail separation theorem remain producer obligations; the generic library does not insert them as axioms.

- **boundary**: Filtration has one public definition in Internal/Algebra/Filtration/Data.lean. Filtered complexes, convergence, completion and truncation use this same type; the former Algebra.Filtration record and bidirectional conversion wrappers are removed.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.