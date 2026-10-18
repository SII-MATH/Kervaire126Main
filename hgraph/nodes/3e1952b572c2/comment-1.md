---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: page-labels-and-finite-state
title: 'Interface scope: page-labels-and-finite-state'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `page-labels-and-finite-state`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Express named E₂ labels, later-page representatives, cycles, boundaries, nonzero finite survival and specified differentials.

- **interface_role**: Predicates state actual properties of a supplied sequence; the public theorems derive consequences without adding assumptions to a global model.

- **mathematical_strength_preserved**: RepresentsOnPage requires one cycle representative for the E₂ and Eᵣ labels, with 2 ≤ r. There is no map from all of E₂ to Eᵣ.

- **mathematical_strength_preserved**: SurvivesTo means a nonzero continuation on that page; ReachesPage permits zero. Survival to Eᵣ does not assert dᵣ=0.

- **mathematical_strength_preserved**: HasDifferential allows a zero target; HasNonzeroDifferential requires the actual later-page target to be nonzero.

- **mathematical_strength_preserved**: IsPageBoundary includes zero. NeverHit excludes only nonzero incoming hits and does not eliminate outgoing differentials.

- **mathematical_strength_preserved**: DifferentialVanishesOn and DifferentialTargets quantify over continuations and do not assert that any continuation exists.

- **boundary**: The bidegree specialization is kept for existing classical labels; no speculative rewrite of every element predicate to a general grading is required for current synthetic consumers.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.