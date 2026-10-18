---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: ambient-differential-relations
title: 'Interface scope: ambient-differential-relations'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `ambient-differential-relations`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Describe the actual differential using ambient representatives and identify its complete target boundary coset.

- **interface_role**: Generic categorical representative relations and proved coset operations, usable by bounded ESS consumers.

- **mathematical_strength_preserved**: DifferentialRelation supplies actual cycle lifts of both ambient labels whose quotient images satisfy the actual differential equation.

- **mathematical_strength_preserved**: DifferentialTargetCoset is the full translate by the actual target Bᵣ subobject. Given one relation, membership is equivalent to another relation with the same source.

- **mathematical_strength_preserved**: EssentialDifferentialRelation means the target does not factor through that boundary; the proved criterion excludes zero from the full target coset.

- **boundary**: The broader private crossing predicates are not exported as replacements for Adams page-extension crossing: their quantifiers and exact filtration constraints differ.

- **boundary**: The generic relation is not an arbitrary user-supplied Prop field and does not discard the actual spectral-sequence differential.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.