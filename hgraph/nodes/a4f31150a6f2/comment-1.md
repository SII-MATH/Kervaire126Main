---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: Computation
title: Module interface conventions
updated: '2026-10-17T17:47:44'
---
Module-level interface conventions; completion remains derived from verified Lean evidence.

- **principle**: 普通公共导入即可调用同一固定背景上的对象与定理；下游不传入结果包。保留真正数学前提；未完成构造与证明逐项登记，不能把可调用误报为已证明。

- **type_authority**: metadata/computation-api.json

- **exclusions**: No Main conclusion or global witness axiom.

- **exclusions**: No README/AGENTS/Blueprint changes.