---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: generic-sequence-signatures
title: 'Interface scope: generic-sequence-signatures'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `generic-sequence-signatures`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Given a spectral sequence in an abelian category: actual pages, differential, cycle/boundary towers and successor homology.

- **interface_role**: SpectralSequence is supplied data with structural laws. SSData, PreSS and GradedComplex remain signature foundations, not an assertion that a concrete Adams model has been constructed.

- **mathematical_strength_preserved**: Page r is the specified Z/B quotient with its actual quotient map; d squares to zero and respects the declared differential degree.

- **mathematical_strength_preserved**: The same ambient SSData supports all finite pages and E∞. The successor-page compatibility is retained in the SpectralSequence fields.

- **mathematical_strength_preserved**: The core is generic in the abelian category and grading group. The specialized element-label predicates remain over ModuleCat R and bidegrees; synthetic tridegrees use this generic core directly.

- **boundary**: No public ofPreSS or DifferentialMorphismCriterion construction adapter.

- **boundary**: SSData cannot be made private while its V/Z/B/pageπ fields form these mathematical signatures.

- **boundary**: Unconsumed EInftyData and GradedSSData convenience wrappers are private; they are not needed to state the retained contracts.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.