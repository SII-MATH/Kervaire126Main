module

import KIP126
import Lean

/-! Public consumers of the migrated four-directory API. The endpoint is the
same fixed standard nonzero-survival statement as in develop. -/
open KIP126.Classical.Adams KIP126.SpectralSequence

example : NonzeroSurvival sphereAdamsData (2, 128) standardH6Square :=
  KIP126.Main.h6_sq_permanent

example : KIP126.Main.externalHypotheses.literature =
    KIP126.Literature.adamsSyntheticResults := rfl

example : KIP126.Main.externalHypotheses.computation =
    KIP126.Computation.adamsComputations := rfl

example : sphereAdamsData =
    KIP126.Classical.Adams.adamsTowerInternalSpectralSequence
      standardFoundation.hf2.unit KIP126.StableHomotopy.SphereSpectrum := rfl

example : standardH6Square =
    Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 6 := rfl

example : sphereAdamsData.r₀ = 2 := rfl

example (r : ℤ) : sphereAdamsData.diffDeg r = (r, r - 1) := rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for obsolete in [`KIP126.Implementation, `KIP126.Challenge2,
      `KIP126.Main.Axiom.challenge2, `KIP126.Main.StageInput.witness] do
    if (env.find? obsolete).isSome then
      throwError "Obsolete public mathematical API: {obsolete}"
  for result in [``KIP126.Main.proposition_7_8,
      ``KIP126.Main.SectionSeven.proposition_7_9] do
    unless wasOriginallyTheorem env result do
      throwError "Paper result must remain a proved theorem: {result}"
  let target := ``KIP126.Main.h6_sq_permanent
  let some ti := env.find? target | throwError "Missing final h6-square theorem"
  -- The module system exports theorem stubs with their original kind recorded
  -- separately; inspecting the exported ConstantInfo constructor is insufficient.
  unless wasOriginallyTheorem env target do
    throwError "The final conclusion must be declared as a theorem"
  if ti.type.isForall then
    throwError "The final theorem acquired caller hypotheses"
  unless ti.type.getUsedConstants.contains ``KIP126.Classical.Adams.standardH6Square &&
      ti.type.getUsedConstants.contains ``KIP126.SpectralSequence.NonzeroSurvival do
    throwError "The final target must be standard h6 square nonzero survival"
  unless wasOriginallyDefn env ``KIP126.Main.externalHypotheses do
    throwError "The combined ExternalHypotheses must be a definition pairing the two external hypotheses"
  for name in [``KIP126.Literature.adamsSyntheticResults, ``KIP126.Computation.adamsComputations] do
    let some info@(.axiomInfo _) := env.find? name
      | throwError "Missing explicit external-result axiom: {name}"
    unless getOriginalConstKind? env name == some (ConstantKind.ofConstantInfo info) do
      throwError "External assumption must be an actual source axiom: {name}"
  -- Generic objects belong to Def. The closed standard objects specialize
  -- those constructions using the two explicitly selected background models.
  -- Literature/computation conclusions must not determine the target itself.
  let mut pending := ti.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing target dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf owner do continue
    unless (`KIP126.Def).isPrefixOf owner ||
        (`KIP126.Literature.Standard).isPrefixOf owner ||
        (`KIP126.Literature.Background).isPrefixOf owner do
      throwError "Final statement depends on a result or proof module: {name}: {owner}"
    if info.isAxiom &&
        getOriginalConstKind? env name == some (ConstantKind.ofConstantInfo info) then
      unless [``KIP126.StableHomotopy.Spectra.completionModel_exists,
          ``KIP126.AdamsSynthetic.hf2AdamsContext_exists].contains name do
        throwError "Final statement depends on an external result axiom: {name}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  logInfo "Architecture: unchanged fixed standard target; only registered background choices in its type; two correlated external result hypotheses"
