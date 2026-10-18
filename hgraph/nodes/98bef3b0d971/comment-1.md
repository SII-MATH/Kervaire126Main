---
author: metadata-migration
created: '2026-10-17T17:47:29'
date: '2026-10-17T17:47:29'
owner_module: SpectralSequence
scope_id: page-and-length-indices
title: 'Interface scope: page-and-length-indices'
updated: '2026-10-17T17:47:29'
---
Scope of the related interface family `page-and-length-indices`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Distinguish valid Adams display pages from nonnegative extension lengths and their grading conventions.

- **interface_role**: Public value types, explicit conversions and arithmetic laws; no implicit identification of length zero with an Adams page.

- **mathematical_strength_preserved**: AdamsPage contains a proof that its natural value is at least two; ExtensionLength permits zero.

- **mathematical_strength_preserved**: The conversion from an extension length to an Adams page requires its own lower-bound proof.

- **mathematical_strength_preserved**: PageLevelConvention retains separate page, cycle-level and quotient-exponent functions and successor laws.

- **boundary**: Current new AdamsSynthetic consumers express their exact inequalities directly in Lean; no claim is made that they already use these wrapper types.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843). Exact original source blocks and migration history remain in `local-history/metadata/spectral-sequence-sources.json`.