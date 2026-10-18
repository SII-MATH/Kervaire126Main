---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: AdamsSynthetic
scope_id: obligation-zlambda-enrichment
title: 'Interface scope: obligation-zlambda-enrichment'
updated: '2026-10-17T17:47:44'
---
Scope of the related interface family `obligation-zlambda-enrichment`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: Hom 分量就是 Hom(Σ^(0,w) X,Y)，总 Hom 是这些实际 Hom 的直和；不是任意新选对象。 Polynomial.X 在直和注入上等于由同一 lam 和同一 shift comparison 构成的 weightHomLambda；权重降低一。 复合是 ℤ[λ] 双线性，齐次分量上的复合等于实际移位映射复合；单位由同一 biShift_zero 得到。 修正旧未分次 EnrichedCategory(ModuleCat ℤ[λ]) 的语义：普通 Syn 是分次富集的零次部分；不宣称 λ 是固定权重 Hom 上的自映射。 结合律和左右单位律从同一 shift coherence、齐次实际复合相容式及 DirectSum 加法归纳推导，已经删除重复输入字段。

- **constraints**: Hom 分量就是 Hom(Σ^(0,w) X,Y)，总 Hom 是这些实际 Hom 的直和；不是任意新选对象。 Polynomial.X 在直和注入上等于由同一 lam 和同一 shift comparison 构成的 weightHomLambda；权重降低一。 复合是 ℤ[λ] 双线性，齐次分量上的复合等于实际移位映射复合；单位由同一 biShift_zero 得到。 修正旧未分次 EnrichedCategory(ModuleCat ℤ[λ]) 的语义：普通 Syn 是分次富集的零次部分；不宣称 λ 是固定权重 Hom 上的自映射。 结合律和左右单位律从同一 shift coherence、齐次实际复合相容式及 DirectSum 加法归纳推导，已经删除重复输入字段。

- **constraints**: 旧未分次富集声明没有绑定权重；新合同在 ⨁ w, Hom(Σ^(0,w) X,Y) 上交付 ℤ[λ] 富集，并将普通 Syn 解释为零次部分。λ 降权一，不能在固定权重 Hom 内强行当作自映射。

- **constraints**: User-approved exception: graded_compose is no_expose; its mathematical signature and homogeneous formula remain available, and the frozen graded_compose._proof_1 full type/name must remain exact. No other new public support declaration is authorized.

- **roles**: explicit-input-or-derived-consumer-contract


Code provenance: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSource871b3be8f46a](https://github.com/SII-MATH/Kervaire126/tree/871b3be8f46a1c02d49011e9c6495ec3d938b338), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Exact original source blocks and migration history remain in `local-history/metadata/adams-synthetic-sources.json`.