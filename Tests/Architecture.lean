module

import KIP126
import Lean

/-! The ordinary root import exposes all eight mathematical modules and the
standard-family theorem on the fixed background. Module-specific consumers retain their own checks;
Tests.Integration separately checks consumption without importing Main. -/

open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

example : NonzeroSurvival model.classical.sphere (2, 128)
    model.standardClasses.standardH6Square :=
  KIP126.Main.h6_sq_permanent model.standardClasses

example : KIP126.Literature.Geometry.KervaireInvariantOneExists 126 :=
  KIP126.Geometry.kervaire_invariant_one_126

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let entries := #[`KIP126.SpectralSequence, `KIP126.AdamsSynthetic,
    `KIP126.Literature, `KIP126.E2Computation, `KIP126.ProofTools,
    `KIP126.AdamsCalculations, `KIP126.Main, `KIP126.Geometry]
  for entry in entries do
    unless env.header.moduleNames.contains entry do
      throwError "Root import is missing a public module: {entry}"
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod && mod != `KIP126 &&
        !(entries.any (·.isPrefixOf mod)) then
      throwError "Root import includes an unowned project module: {mod}"
  let target := ``KIP126.Main.h6_sq_permanent
  let some info := env.find? target | throwError "Missing final h6-square theorem"
  unless wasOriginallyTheorem env target do
    throwError "The final conclusion must remain a theorem"
  match info.type with
  | .forallE _ _ _ .default => pure ()
  | _ => throwError "The final theorem must take one explicit standard-class family"
  liftTermElabM do
    Meta.forallTelescope info.type fun args _ => do
      unless args.size == 1 do
        throwError "The final theorem acquired parameters beyond its standard-class family"
    let expected ← Term.elabType (← `(∀
      (H : KIP126.Classical.Adams.StandardSphereClasses
        KIP126.AdamsSynthetic.Standard.classical
        KIP126.AdamsSynthetic.Standard.sphereAlgebra),
      NonzeroSurvival KIP126.AdamsSynthetic.Standard.classical.sphere (2,128)
        (KIP126.AdamsSynthetic.Standard.sphereAlgebra.product (1,64) (1,64)
          (H.hi 6) (H.hi 6))))
    unless ← Meta.isDefEq info.type expected do
      throwError "The final theorem changed its standard-class parameter, fixed background or product conclusion"
  -- Only generic spectral-sequence objects and the fixed Adams background may
  -- determine the statement. Literature and computation supply its proof.
  -- Dependency inspection needs private constant data as well as public exports.
  -- The consumer examples and statement checks above still use the ordinary import.
  let opts ← getOptions
  let auditEnv ← liftIO <| Lean.importModules #[{ module := `KIP126 }] opts
    (loadExts := false) (level := .private)
  let some auditInfo := auditEnv.find? target |
    throwError "Missing final h6-square theorem in the dependency-audit environment"
  unless auditInfo.type == info.type do
    throwError "Dependency-audit environment changed the fixed final target type"
  let mut pending := info.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some dependency := auditEnv.find? name | throwError "Missing target dependency: {name}"
    let some idx := auditEnv.getModuleIdxFor? name | continue
    let owner := auditEnv.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf owner do continue
    unless (`KIP126.SpectralSequence).isPrefixOf owner ||
        (`KIP126.AdamsSynthetic).isPrefixOf owner do
      throwError "Final statement depends on a result or proof module: {name}: {owner}"
    pending := pending ++ dependency.type.getUsedConstants
    if let some value := dependency.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  logInfo "Architecture: eight mathematical modules; standard-family target uses only its fixed upstream objects"
