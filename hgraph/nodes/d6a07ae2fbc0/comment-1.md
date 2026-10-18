---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: filtered-map-extensions
title: 'Interface scope: filtered-map-extensions'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `filtered-map-extensions`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Use extension equations, actual lifts, complete target indeterminacy and essentiality for one specified filtered map.

- **interface_role**: New public consumer wrapper over existing mathematical semantics, with all operation laws proved. ConvergenceMorphism.filteredMap extracts the same abutment map and compatibility witness.

- **mathematical_strength_preserved**: Relation f k s n x y requires 0 ≤ n and actual a in Fˢ, b in Gˢ⁺ⁿ with the specified quotient labels and the exact equation a ≫ inclusion ≫ f.map = b ≫ inclusion.

- **mathematical_strength_preserved**: TargetIndeterminacy consists exactly of homogeneous Relation f ... 0 z solutions. mem_indeterminacy_iff identifies it with actual source lifts in Fˢ⁺¹ mapped into Gˢ⁺ⁿ by the same f.

- **mathematical_strength_preserved**: Given one solution, TargetCoset is the entire set of possible targets for that source, not a chosen subspace of ambiguity.

- **mathematical_strength_preserved**: Essential excludes zero from that full target coset and is equivalent to the absence of a zero-target relation.

- **mathematical_strength_preserved**: For arbitrary probe T, a zero-length relation is equivalent to both source quotient-lift existence and the induced associated-graded map equation.

- **mathematical_strength_preserved**: Only with Projective T can source lift existence be discharged and the zero-length criterion reduce to the graded equation.

- **boundary**: No new property field claims these consequences without proof; the generic operations are theorems.

- **boundary**: The wrapper is independent of concrete filtered-complex construction while its bridge proves equivalence to the original solution fiber.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.