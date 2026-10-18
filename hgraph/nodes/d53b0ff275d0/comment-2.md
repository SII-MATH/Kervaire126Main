---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: SpectralSequence
title: Module interface conventions
updated: '2026-10-17T17:47:44'
---
Module-level interface conventions; completion remains derived from verified Lean evidence.

- **principle**: Generic spectral-sequence definitions and proved operations retain genuine mathematical parameters. Project consumers obtain their fixed sequence and comparisons from AdamsSynthetic.Standard. SpectralSequence has no admitted declarations.

- **type_authority.api_manifest**: metadata/spectral-sequence-api.json

- **type_authority.source_manifest**: metadata/spectral-sequence-sources.json

- **type_authority.rule**: Exact elaborated types, universe levels and typeclass assumptions are frozen by the API manifest and Lean source. This ledger classifies purpose and evidence; abbreviated mathematical prose is not a replacement signature.

- **classification.mathematical-definition-or-operation**: An explicit public definition, predicate, data structure, abbreviation or operation that states or operates on a mathematical contract.

- **classification.proved-operation**: An explicit public theorem/lemma whose conclusion is derived from the declared hypotheses. The capture kind field alone does not reliably distinguish these from compiler-generated declarations.

- **classification.required-type-support**: Explicit foundational structures or instances needed to state or use retained signatures, including SSData, PreSS, underlying morphism records, and the public categories. They are not counted as independent domain capabilities.

- **classification.generated-signature-support**: Lean-emitted structure fields, constructors, parent projections and required instances. These may be essential mathematical inputs even though they are emitted automatically; associate them with the owning explicit structure.

- **classification.generated-elaboration-support**: Recursors, noConfusion, equation lemmas, auxiliary _proof declarations and derived compiler helpers. These do not independently justify an additional consumer-facing mathematical capability.

- **classification.counting_rule**: Do not equate export count, explicit public-command count or compiler-generated declaration count with the number of contracts. Do not use numerical reduction alone to justify hiding a mathematical operation.

- **private_implementation_boundary**: FilteredComplex construction and its representative/fiber machinery

- **private_implementation_boundary**: BoundedExtension.underlyingComplex and compatibility construction proofs

- **private_implementation_boundary**: ModuleSubobject and ModuleQuotient construction lemmas

- **private_implementation_boundary**: DifferentialMorphismCriterion and ofPreSS adapters

- **private_implementation_boundary**: Generic crossing predicates whose mathematical strength does not coincide with the precise Adams page-extension contracts

- **private_implementation_boundary**: Algebra support under SpectralSequence/Internal/Algebra; only retained SpectralSequence contracts and the F2 coefficient alias are public.