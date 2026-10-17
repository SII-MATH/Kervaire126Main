# Lean 4.32.2 exposed data proof packaging: read-only source review

Target: `KIP126.Literature.Standard.tmf_convergence : ClassicalTowerConvergence model.classicalTower tmf`.
Git baseline: `bef90640c4594af4db32c86837f9d95340d1e171`; task-supplied Standard source SHA-256: `8ba89e65cd91d11783ea3aa08fc83f5891337c1f7aaa6e8abfb39ae440072bd6`.
Protocol: `/root/.agents/skills/kip-upstream-session/references/protocol.md`.
Scope: read installed Lean compiler sources; do not run Lean/Lake and do not edit production files.

## Result

No source option disables the complete nested-proof extraction pipeline for an exposed data definition. The existing `backward.proofsInPublic` option controls a separate earlier tactic elaboration step; using it alone does not solve the frozen-export problem. Private theorem applications are unavailable in a public exposed data body and, if injected, the final extractor recognizes the missing public constant and abstracts it again. Enabling `backward.privateInPublic` would really export private declarations, so it changes the boundary and is excluded.

My initial message that there was no local proof-extraction option at all was too broad: the option below exists, but controls only the first of two stages. This report supersedes that preliminary wording.

## Source paths and semantics

Source root: `/root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/`.

1. `Lean/Elab/SyntheticMVars.lean:458–463` registers `backward.proofsInPublic : Bool`, default false. `runTactic` at lines 474–526 switches out of exporting context for a Prop goal, unless this option is true. After elaborating a non-fvar proof it switches back to exporting and calls `mkAuxTheorem`. Consequently even `by exact private_helper ...` produces an exported auxiliary proof with the default setting. A mere fvar is the exception.
2. `Lean/Elab/PreDefinition/Basic.lean:120–127` applies `Meta.abstractNestedProofs` to any declaration other than theorem/example, and `addNonRecAux` at line 183 invokes it unconditionally. The `cacheProofs` argument only controls caching.
3. `Lean/Meta/AbstractNestedProofs.lean:40–66` calls a proof trivial only if, after dropping lambdas, its application head and all arguments are atomic, and any constant head is present in the original environment. `visit` at lines 94–98 extracts every nontrivial proof without sorry via `abstractProof`; `abstractNestedProofs` at lines 111–117 skips extraction only when the whole definition value itself is a proof.
4. `Lean/Expr.lean:1517–1525` says atomic means const/sort/bvar/literal/mvar/fvar. Applications, lambdas, let expressions, projections, and metadata wrappers are not atomic.
5. `Lean/ResolveName.lean:119–124,283–285` prevents access to private names in exporting context unless `backward.privateInPublic` is enabled. Thus `backward.proofsInPublic=true` keeps tactic elaboration public and makes private helper names unavailable.
6. `Lean/AddDecl.lean:136–142` shows why `backward.privateInPublic` is not a harmless visibility annotation: a private declaration is actually installed in the public environment with its full ConstantInfo when the option is true. It must not be used to evade the module boundary or interface freeze.
7. `Lean/Meta/Tactic/AuxLemma.lean:40–65` creates `_proof` auxiliary declarations using the current exporting setting. A theorem type gets exported as an axiom interface by `Lean/AddDecl.lean:111–115`; that is Lean module packaging, not a newly authorized project mathematical axiom, but the additional public name still changes the export set.
8. `Lean/Environment.lean:839–850,1145–1146` makes `find?`/`contains` respect the public environment and `hasExposedBody` explicitly checks the exporting environment. A normal public consumer is therefore required; checking only the private environment would not establish exposure.

## Consequences for a faithful implementation

The safe source-level route is a direct data term whose proof subterms use already-public theorem constants in trivial applications. Intermediate data/proof values may be bound in the outer data construction so that subsequent applications use atomic fvars; a complex entire proof lambda or proof-local let still becomes a nontrivial proof. A private theorem can assist proof-only public theorems, but cannot serve as a transparent shortcut for this public data body under the strict module boundary.

No recommendation here changes the target type, witness, object, exposure, public names, interface locks, or checks. No production edit, Lean probe, build, or mathematical proof verification was performed by this subagent.

## Minimal probes for the coordinator (not run here)

Use a module file and a structure with a genuine data field and a Prop field. Compare: (a) public def using an inline `by` Prop proof at default settings, (b) locally set `backward.proofsInPublic=true` with an existing public theorem whose elaborated application has atomic arguments, (c) the same option with a private theorem, which should fail name resolution, (d) an existing public theorem applied to a non-atomic argument, which can still trigger final nested extraction. For successful variants, an independent normal public import should count declarations and check `hasExposedBody`; neither same-module private access nor compilation alone suffices.

## Installed compiler source hashes

- `Lean/Meta/AbstractNestedProofs.lean`: `0c15c160c399770e90c209bfd23944855dd888811ab7cf4aa0a3e81ec7bf92df`
- `Lean/Elab/PreDefinition/Basic.lean`: `fc5ab30e72ff2bff02a2447ae7f828bdcbe316b428ee4a923ce0f622dd52ba63`
- `Lean/Elab/SyntheticMVars.lean`: `e33b9ec83b5ca5108b910419fda0492a36a7837cb205d7594429fb6ed9ea22fc`
- `Lean/ResolveName.lean`: `c42a2e8e21b0d0325a32f09827be6253aad276ac4d25b30b5281b420f1beccb9`
- `Lean/AddDecl.lean`: `db9e450202be18ec6870d28c2cc2e7aeda5bfc22a0eb1747e2fcca06f548b905`
