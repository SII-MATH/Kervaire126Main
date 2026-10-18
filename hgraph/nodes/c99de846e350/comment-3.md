---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: AdamsSynthetic
title: Module interface conventions
updated: '2026-10-17T17:47:44'
---
Module-level interface conventions; completion remains derived from verified Lean evidence.

- **principle**: 普通公共导入即可调用同一固定背景上的对象与定理；下游不传入结果包。保留真正数学前提；未完成构造与证明逐项登记，不能把可调用误报为已证明。

- **type_authority**: Complete types and universe/typeclass assumptions live in the referenced Lean declarations. The API manifest and normal-import tests freeze their elaborated types; this semantic ledger is not a second Lean source registry.

- **exclusions**: README and AGENTS edits

- **exclusions**: Blueprint migration/checks

- **exclusions**: Literature/Computation/ProofTools/Main implementations

- **exclusions**: raw CSV/Generated/checkers

- **exclusions**: full completion-model identification and derived-source unitor are explicit unfinished source tasks

- **weight_direction_correction.statement**: For w1≤w2≤t, the quotient and actual lambda map lower weight w2→w1.

- **weight_direction_correction.reason**: B_(1+t-w2) ≤ B_(1+t-w1); the old reverse quotient map was not well-defined in general.

- **weight_direction_correction.affected_type**: KIP126.AdamsSynthetic.NuInfinityWeightMaps

- **weight_direction_correction.compatibility**: Intentional signature correction; former type freeze updated and tracking retained.

- **nu_cofiber_condition_correction.statement**: NuExactTriangleInput requires injectivity, middle exactness and surjectivity in every HF2-homology degree.

- **nu_cofiber_condition_correction.reason**: Middle exactness of a distinguished triangle alone does not imply that nu preserves its cofiber.

- **nu_cofiber_condition_correction.affected_type**: KIP126.AdamsSynthetic.NuExactTriangleInput.preserves

- **nu_cofiber_condition_correction.compatibility**: Intentional correction of an overly strong legacy input; the same predicate is reused by the full Literature iff.