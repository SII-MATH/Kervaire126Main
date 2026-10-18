module

import KIP126
import Lean

/-! The ordinary root import exposes all eight mathematical modules and the
fixed standard target. Module-specific consumers retain their own checks;
Tests.Integration separately checks consumption without importing Main. -/

open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

example : NonzeroSurvival model.classical.sphere (2, 128)
    model.standardClasses.standardH6Square := KIP126.Main.h6_sq_permanent

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
  if info.type.isForall then
    throwError "The fixed final theorem acquired caller hypotheses"
  -- Only generic spectral-sequence objects and the fixed Adams background may
  -- determine the statement. Literature and computation supply its proof.
  let mut pending := info.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some dependency := env.find? name | throwError "Missing target dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf owner do continue
    unless (`KIP126.SpectralSequence).isPrefixOf owner ||
        (`KIP126.AdamsSynthetic).isPrefixOf owner do
      throwError "Final statement depends on a result or proof module: {name}: {owner}"
    pending := pending ++ dependency.type.getUsedConstants
    if let some value := dependency.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  logInfo "Architecture: eight mathematical modules; fixed standard target uses only its upstream objects"
