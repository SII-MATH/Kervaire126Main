## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Elab/SyntheticMVars.lean:458–526
Full source SHA-256: e33b9ec83b5ca5108b910419fda0492a36a7837cb205d7594429fb6ed9ea22fc

```lean
458: register_builtin_option backward.proofsInPublic : Bool := {
459:   defValue := false
460:   descr    := "(module system) Do not abstract proofs used in the public scope into auxiliary \
461:     theorems. Enabling this option may lead to failures or, when `backward.privateInPublic` and \
462:     its `warn` sub-option are enabled, additional warnings from private accesses."
463: }
464: 
465: mutual
466: 
467:   /--
468:   Try to synthesize a term `val` using the tactic code `tacticCode`, and then assign `mvarId := val`.
469: 
470:   The `tacticCode` syntax comprises the whole `by ...` expression.
471: 
472:   If `report := false`, then `runTactic` will not capture exceptions nor will report unsolved goals. Unsolved goals become exceptions.
473:   -/
474:   partial def runTactic (mvarId : MVarId) (tacticCode : Syntax) (kind : TacticMVarKind) (report := true) : TermElabM Unit := withoutAutoBoundImplicit do
475:     let wasExporting := (← getEnv).isExporting
476:     -- exit exporting context if entering proof
477:     let isNoLongerExporting ← pure (wasExporting && !(← backward.proofsInPublic.getM)) <&&> do
478:       mvarId.withContext do
479:         isProp (← mvarId.getType)
480:     instantiateMVarDeclMVars mvarId
481:     -- When exiting exporting context, use fresh mvar for running tactics and abstract it into an
482:     -- aux theorem in the end so that we cannot leak references to private decls into the exporting
483:     -- context.
484:     let mut mvarId' := mvarId
485:     if isNoLongerExporting then
486:       let mvarDecl ← getMVarDecl mvarId
487:       mvarId' := (← mkFreshExprMVarAt mvarDecl.lctx mvarDecl.localInstances mvarDecl.type mvarDecl.kind).mvarId!
488:     withExporting (isExporting := wasExporting && !isNoLongerExporting) do
489:     /-
490:     TODO: consider using `runPendingTacticsAt` at `mvarId` local context and target type.
491:     Issue #1380 demonstrates that the goal may still contain pending metavariables.
492:     It happens in the following scenario we have a term `foo A (by tac)` where `A` has been postponed
493:     and contains nested `by ...` terms. The pending metavar list contains two metavariables: ?m1 (for `A`) and
494:     `?m2` (for `by tac`). When `A` is resumed, it creates a new metavariable `?m3` for the nested `by ...` term in `A`.
495:     `?m3` is after `?m2` in the to-do list. Then, we execute `by tac` for synthesizing `?m2`, but its type depends on
496:     `?m3`. We have considered putting `?m3` at `?m2` place in the to-do list, but this is not super robust.
497:     The ideal solution is to make sure a tactic "resolves" all pending metavariables nested in their local context and target type
498:     before starting tactic execution. The procedure would be a generalization of `runPendingTacticsAt`. We can try to combine
499:     it with `instantiateMVarDeclMVars` to make sure we do not perform two traversals.
500:     Regarding issue #1380, we addressed the issue by avoiding the elaboration postponement step. However, the same issue can happen
501:     in more complicated scenarios.
502:     -/
503:     tryCatchRuntimeEx
504:       (do let remainingGoals ← withInfoHole mvarId <| Tactic.run mvarId' <| kind.maybeWithoutRecovery do
505:             withTacticInfoContext tacticCode do
506:               -- also put an info node on the `by` keyword specifically -- the token may be `canonical` and thus shown in the info
507:               -- view even though it is synthetic while a node like `tacticCode` never is (#1990)
508:               withTacticInfoContext tacticCode[0] do
509:                 withNarrowedArgTacticReuse (argIdx := 1) (evalTactic ·) tacticCode
510:             -- Pending tactic mvars may escape from `evalTactic` to here (#4436), so make sure
511:             -- incrementality is disabled so they cannot be confused for top-level tactic blocks
512:             withoutTacticIncrementality true do
513:               synthesizeSyntheticMVars (postpone := .no)
514:           unless remainingGoals.isEmpty do
515:             if report then
516:               kind.logError tacticCode
517:               reportUnsolvedGoals remainingGoals
518:             else
519:               throwError "unsolved goals\n{goalsToMessageData remainingGoals}"
520:           if isNoLongerExporting then
521:             let mut e ← instantiateExprMVars (.mvar mvarId')
522:             if !e.isFVar then
523:               e ← mvarId'.withContext do
524:                 withExporting (isExporting := wasExporting) do
525:                   -- Like `abstractProof`, but use the expected and not given type here as
526:                   -- the latter might not make sense outside the current module (#11672).
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Elab/PreDefinition/Basic.lean:119–128
Full source SHA-256: fc5ab30e72ff2bff02a2447ae7f828bdcbe316b428ee4a923ce0f622dd52ba63

```lean
119: 
120: def abstractNestedProofs (preDef : PreDefinition) (cache := true) : MetaM PreDefinition := withRef preDef.ref do
121:   if preDef.kind.isTheorem || preDef.kind.isExample then
122:     pure preDef
123:   else do
124:     let value ←
125:       withDeclNameForAuxNaming preDef.declName do
126:         Meta.abstractNestedProofs (cache := cache) preDef.value
127:     pure { preDef with value := value }
128: 
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Elab/PreDefinition/Basic.lean:173–189
Full source SHA-256: fc5ab30e72ff2bff02a2447ae7f828bdcbe316b428ee4a923ce0f622dd52ba63

```lean
173: -/
174: def addPreDefInfo (preDef : PreDefinition) : TermElabM Unit := do
175:   withSaveInfoContext do  -- save new env that includes docstring and constant
176:     addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
177: 
178: 
179: private def addNonRecAux (docCtx : LocalContext × LocalInstances) (preDef : PreDefinition) (compile : Bool)
180:     (all : List Name) (applyAttrAfterCompilation := true) (cacheProofs := true) (cleanupValue := false)
181:     (isRecursive := false) : TermElabM Unit :=
182:   withRef preDef.ref do
183:     let preDef ← abstractNestedProofs (cache := cacheProofs) preDef
184:     let preDef ← letToHaveType preDef
185:     let preDef ← if cleanupValue then letToHaveValue preDef else pure preDef
186:     let mkDefDecl : TermElabM Declaration :=
187:       return Declaration.defnDecl {
188:           name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value
189:           hints := ReducibilityHints.regular (getMaxHeight (← getEnv) preDef.value + 1)
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Meta/AbstractNestedProofs.lean:34–117
Full source SHA-256: 0c15c160c399770e90c209bfd23944855dd888811ab7cf4aa0a3e81ec7bf92df

```lean
34: 
35: def getLambdaBody (e : Expr) : Expr :=
36:   match e with
37:   | .lam _ _ b _ => getLambdaBody b
38:   | _ => e
39: 
40: def isNonTrivialProof (e : Expr) : MetaM Bool := do
41:   let origEnv ← getEnv
42:   -- NOTE: this `withoutExporting` is not strictly necessary when considering the Lean elaborator
43:   -- per se because there `e` is an elaboration result that should have been produced under the same
44:   -- `Environment.isExporting` setting as the current one, so all referenced constants should be
45:   -- accessible as is. However, Mathlib's `[to_additive]`, for example, uses `abstractNestedProofs`
46:   -- on terms that contain the unfolding of non-exposed definitions and so may reference private
47:   -- declarations but the code might still be run under `isExporting = true` in order to create the
48:   -- new aux decls in the public scope. Thus we always shift to the private scope here.
49:   withoutExporting do
50:   if !(← isProof e) then
51:     return false
52:   else if e.isAppOf ``Grind.nestedProof then
53:     -- Grind.nestedProof is a gadget created by the `grind` tactic.
54:     -- We want to avoid the situation where `grind` keeps creating them,
55:     -- and this module, which is used by `grind`, keeps abstracting them.
56:     return false
57:   else
58:     -- We consider proofs such as `fun x => f x a` as trivial.
59:     -- For example, we don't want to abstract the body of `def rfl`
60:     (getLambdaBody e).withApp fun f args =>
61:       pure $ !f.isAtomic ||
62:         -- Again we may need to re-do an abstraction here for `to_additive` even if in base
63:         -- elaborator, this condition should never be fulfilled
64:         f.const?.any (!origEnv.contains ·.1) ||
65:         args.any fun arg => !arg.isAtomic
66: 
67: structure Context where
68:   cache    : Bool
69: 
70: abbrev M := ReaderT Context $ MonadCacheT ExprStructEq Expr MetaM
71: 
72: partial def visit (e : Expr) : M Expr := do
73:   checkSystem "abstract nested proofs"
74:   if e.isAtomic then
75:     pure e
76:   else
77:     let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do
78:       let localInstances ← getLocalInstances
79:       let mut lctx ← getLCtx
80:       for x in xs do
81:         let xFVarId := x.fvarId!
82:         let localDecl ← xFVarId.getDecl
83:         let type      ← visit localDecl.type
84:         let localDecl := localDecl.setType type
85:         let localDecl ← match localDecl.value? (allowNondep := true) with
86:            | some value => let value ← visit value; pure <| localDecl.setValue value
87:            | none       => pure localDecl
88:         lctx := lctx.modifyLocalDecl xFVarId fun _ => localDecl
89:       withLCtx lctx localInstances k
90:     checkCache { val := e : ExprStructEq } fun _ => do
91:       if (← isNonTrivialProof e) && !e.hasSorry then
92:         /- Ensure proofs nested in type are also abstracted.
93:            We skip abstraction for proofs containing `sorry` to avoid generating extra
94:            "declaration uses sorry" warnings for auxiliary theorems: one per abstracted proof
95:            instead of a single warning for the main declaration. Additionally, the `zetaDelta`
96:            expansion in `mkAuxTheorem` can inline let-bound sorry values, causing warnings
97:            even for proofs that only transitively reference sorry-containing definitions. -/
98:         abstractProof e (← read).cache visit
99:       else match e with
100:         | .lam ..
101:         | .letE ..     => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b) (usedLetOnly := false) (generalizeNondepLet := false)
102:         | .forallE ..  => forallTelescope e fun xs b => visitBinders xs do mkForallFVars xs (← visit b)
103:         | .mdata _ b   => return e.updateMData! (← visit b)
104:         | .proj _ _ b  => return e.updateProj! (← visit b)
105:         | .app ..      => e.withApp fun f args => return mkAppN (← visit f) (← args.mapM visit)
106:         | _            => pure e
107: 
108: end AbstractNestedProofs
109: 
110: /-- Replace proofs nested in `e` with new lemmas. The new lemmas are named using `getDeclNGen`. -/
111: def abstractNestedProofs (e : Expr) (cache := true) : MetaM Expr := do
112:   if (← isProof e) then
113:     -- `e` is a proof itself. So, we don't abstract nested proofs
114:     return e
115:   else
116:     AbstractNestedProofs.visit e |>.run { cache } |>.run
117: 
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/ResolveName.lean:118–126
Full source SHA-256: c42a2e8e21b0d0325a32f09827be6253aad276ac4d25b30b5281b420f1beccb9

```lean
118: private partial def resolvePrivateName (env : Environment) (opts : Options) (declName : Name) : Option Name := do
119:   -- No point in checking private names when exporting. This is an optimization but also necessary
120:   -- for correct visibility checking while we still carry some private names (e.g. kernel-generated
121:   -- from `inductive`) in the public env.
122:   guard (!env.isExporting || backward.privateInPublic.get opts)
123:   if containsDeclOrReserved env (mkPrivateName env declName) then
124:     return mkPrivateName env declName
125:   -- Under the module system, we assume there are at most a few `import all`s and we can just test
126:   -- them one by one.
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/AddDecl.lean:106–143
Full source SHA-256: db9e450202be18ec6870d28c2cc2e7aeda5bfc22a0eb1747e2fcca06f548b905

```lean
106: 
107:   -- convert `Declaration` to `ConstantInfo` to use as a preliminary value in the environment until
108:   -- kernel checking has finished; not all cases are supported yet
109:   let mut exportedInfo? := none
110:   let (name, info, kind) ← match decl with
111:     | .thmDecl thm =>
112:       if !forceExpose && (← getEnv).header.isModule then
113:         trace[addDecl] "exporting theorem {thm.name} as axiom"
114:         exportedInfo? := some <| .axiomInfo { thm with isUnsafe := false }
115:       pure (thm.name, .thmInfo thm, .thm)
116:     | .defnDecl defn | .mutualDefnDecl [defn] =>
117:       if !forceExpose && (← getEnv).header.isModule && !(← getEnv).isExporting then
118:         trace[addDecl] "exporting definition {defn.name} as axiom"
119:         exportedInfo? := some <| .axiomInfo { defn with isUnsafe := defn.safety == .unsafe }
120:       pure (defn.name, .defnInfo defn, .defn)
121:     | .opaqueDecl op =>
122:       if !forceExpose && (← getEnv).header.isModule && !(← getEnv).isExporting then
123:         trace[addDecl] "exporting opaque {op.name} as axiom"
124:         exportedInfo? := some <| .axiomInfo { op with }
125:       pure (op.name, .opaqueInfo op, .opaque)
126:     | .axiomDecl ax => pure (ax.name, .axiomInfo ax, .axiom)
127:     | _ =>
128:       trace[addDecl] "no matching async adding rules, adding synchronously"
129:       return (← doAdd)
130: 
131:   -- Check early so we can avoid related env ext panics that would happen before the check in the
132:   -- kernel.
133:   if (← getEnv).containsOnBranch name then
134:     throwKernelException <| .alreadyDeclared (← getEnv).toKernelEnv name
135: 
136:   if decl.getTopLevelNames.all isPrivateName then
137:     if (← ResolveName.backward.privateInPublic.getM) then
138:       trace[addDecl] "private decl under `privateInPublic`, exporting as is"
139:       exportedInfo? := some info
140:     else
141:       trace[addDecl] "not exporting private declaration at all"
142:       exportedInfo? := none
143:   else
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Expr.lean:1514–1528
Full source SHA-256: 7d4418bf9fef6f72eac422db70613848f849f074573392e79fb86fe745e79f7e

```lean
1514:   toString := Expr.dbgToString
1515: 
1516: /-- Returns true when the expression does not have any sub-expressions. -/
1517: def isAtomic : Expr → Bool
1518:   | Expr.const .. => true
1519:   | Expr.sort ..  => true
1520:   | Expr.bvar ..  => true
1521:   | Expr.lit ..   => true
1522:   | Expr.mvar ..  => true
1523:   | Expr.fvar ..  => true
1524:   | _             => false
1525: 
1526: end Expr
1527: 
1528: def mkDecIsTrue (pred proof : Expr) :=
```

## /root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Meta/Tactic/AuxLemma.lean:38–68
Full source SHA-256: a48e1a8c42503bf86f0edc9682ab95eb628f6f5608fcb3a3a80abb9b8e6c3c88

```lean
38:   different environment branches, consider using `realizeConst` instead.
39: 
40:   This method is useful for tactics (e.g., `simp`) that may perform preprocessing steps to lemmas provided by
41:   users. For example, `simp` preprocessor may convert a lemma into multiple ones.
42: -/
43: def mkAuxLemma (levelParams : List Name) (type : Expr) (value : Expr) (kind? : Option Name := none)
44:     (cache := true) (inferRfl := false) (forceExpose := false) (defeq := false) : MetaM Name := do
45:   let env ← getEnv
46:   let s := auxLemmasExt.getState env
47:   let key := { type, isPrivate := !env.isExporting, defeq }
48:   let mkNewAuxLemma := do
49:     let auxName ← mkAuxDeclName (kind := kind?.getD `_proof)
50:     let decl :=
51:       if env.hasUnsafe type || env.hasUnsafe value then
52:         -- `result` contains unsafe code, thus we cannot use a theorem.
53:         Declaration.defnDecl {
54:           name        := auxName
55:           hints       := ReducibilityHints.opaque
56:           safety      := DefinitionSafety.unsafe
57:           levelParams, type, value
58:         }
59:       else
60:         Declaration.thmDecl {
61:           name := auxName
62:           levelParams, type, value
63:         }
64:     addDecl (forceExpose := forceExpose) decl
65:     if defeq then defeqAttr.setTag auxName
66:     if inferRfl then
67:       inferDefEqAttr auxName
68:     modifyEnv fun env => auxLemmasExt.modifyState env fun ⟨lemmas⟩ => ⟨lemmas.insert key (auxName, levelParams)⟩
```
