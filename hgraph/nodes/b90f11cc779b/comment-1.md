---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: AdamsSynthetic
scope_id: normalized-extension-language
title: 'Interface scope: normalized-extension-language'
updated: '2026-10-17T17:47:44'
---
Scope of the related interface family `normalized-extension-language`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: 同一actual map的归一化lift及有限/无限延拓见证；未输入传播定理。

- **constraints**: ExtensionEquation is the actual two-term filtered-map solution fiber.

- **constraints**: The full target coset uses the actual shorter-extension boundary subobject, not a selected finite subset.

- **constraints**: Length-zero extension must be derived from the same actual map on E-infinity and canonical convergence naturality.

- **constraints**: Finite witnesses retain page>=2, lower/upper length bounds, source/target cycle levels and common infinity representatives.

- **constraints**: Infinite witnesses retain common permanent representatives and the normalized lower length bound.

- **constraints**: Bounded ESS hypotheses remain separate from general unbounded extension equations.

- **roles**: data

- **roles**: predicate

- **roles**: derived-theorem

- **mathematical_review.finite_cycle_translation**: IsCycle(level) is translated to ReachesPage(level+1). Thus source page r and target page r-n+e retain the old r-1 and r-1-n+e cycle levels. Target page >=2 follows from length_upper.

- **mathematical_review.permanent_translation**: Old permanentCycles is the range of the common Z-infinity representative into E2; IsPermanentCycle preserves that semantics including zero.

- **mathematical_review.normalization**: e(f)=1 iff the same actual target tower admits a stage-one factorization, otherwise zero; no independently supplied filtration integer.

- **mathematical_review.homology_exactness**: HomologyShortExact uses the actual inducedMap (H.object whiskerLeft f); complete injective/exact/surjective conditions correct the old middle-only premise.


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a1c02d49011e9c6495ec3d938b338), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Exact original source blocks and migration history remain in `local-history/metadata/adams-synthetic-sources.json`.