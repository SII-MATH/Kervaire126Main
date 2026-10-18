---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: morphisms-and-naturality
title: 'Interface scope: morphisms-and-naturality'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `morphisms-and-naturality`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Use a single functorial family and its induced maps on ambient objects, cycles, finite pages and E∞.

- **interface_role**: Public morphism records and Category instances give composition and equality; proved naturality operations let downstream transport representative and differential statements.

- **mathematical_strength_preserved**: A spectral-sequence morphism preserves the same cycle/boundary towers and commutes with the actual differential, including degree transport.

- **mathematical_strength_preserved**: Finite-page and infinity maps are induced by that same morphism, not separately supplied unrelated maps.

- **mathematical_strength_preserved**: Identity/composition and representative transport are proved from these records. The PreSS category remains needed by retained PreSSMorphism operation signatures.

- **boundary**: PreSS.forget, equivPreSSMorphism, inclusion, their Full/Faithful witnesses and the duplicate toUnderlying adapter have no current or searched fixed-source consumer; they remain implemented privately.

- **boundary**: Generated parent projections such as SSDataMorphism.toUnderlyingMorphism are signature support and are distinct from the removed hand-written toUnderlying convenience definition.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.