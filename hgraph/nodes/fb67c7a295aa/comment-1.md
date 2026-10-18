---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: Main
title: Module interface conventions
updated: '2026-10-17T17:47:44'
---
Module-level interface conventions; completion remains derived from verified Lean evidence.

- **principle**: 下游直接调用固定上游对象和定理；上游未完成证明或构造仍归上游。本文局部论证保留为 Main／ProofTools 的证明责任；不恢复 Challenge 或结果包参数。

- **type_authority**: metadata/main-api.json

- **exclusions**: Reconstructing concrete Adams/Milnor/cobar or synthetic models as a Main obligation.

- **exclusions**: Re-proving externally cited literature and computation correctness inside Main.

- **exclusions**: Treating a paper-specific conclusion or local Moss application as an upstream external premise.

- **exclusions**: Claiming archived source text, hashes or successful compilation certify completed formal proofs.

- **exclusions**: Restoring Challenge/result-package parameters or adding geometric Kervaire goals.