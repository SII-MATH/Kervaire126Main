---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: bounded-extension-sequence
title: 'Interface scope: bounded-extension-sequence'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `bounded-extension-sequence`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Obtain the extension spectral sequence of the same bounded filtered map and connect its actual differentials to the extension equation.

- **interface_role**: A small opaque public construction and proved comparison interface around the private filtered complex.

- **mathematical_strength_preserved**: Both source and target degreewise boundedness witnesses are explicit and belong to the very same filtrations as f.

- **mathematical_strength_preserved**: The supplied sequence starts at zero and has differential degree (n,-1). sourceIso and targetIso identify its actual ambient objects with the source/target associated grades.

- **mathematical_strength_preserved**: For n : ℕ and Projective T, differentialRelation_iff equates the actual differential relation of this sequence with Relation f, after the specified isomorphisms.

- **mathematical_strength_preserved**: The bridge is proved via the original FilteredComplex.Solutions.Fiber equivalence, retaining its actual-lift semantics and projectivity condition.

- **boundary**: No unbounded ESS construction is asserted. General extension relations remain usable without boundedness.

- **boundary**: No direct current AdamsSynthetic use of sequence is claimed: that module consumes the general extension equation; the bounded ESS bridge is exercised by the ordinary-import SpectralSequence consumer test.

- **boundary**: FilteredComplex, underlyingComplex, solution-fiber implementation and their construction proofs remain private.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.