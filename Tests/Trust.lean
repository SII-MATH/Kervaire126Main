module

import Tests.Architecture
import KIP126
import Lean

/-! Report the real transitive trust boundary. Compilation does not certify that
all project proofs are complete: the exact source holes are recorded in metadata.
No Challenge.Final placeholder may establish the final h6-square theorem. -/
open Lean Elab Command

set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let target := ``KIP126.Main.h6_sq_permanent
  -- This catches goal placeholders even when imported theorem bodies are hidden.
  for owner in env.allImportedModuleNames do
    if (`KIP126.Main.Challenge).isPrefixOf owner ||
        (`KIP126.Def.Challenge).isPrefixOf owner then
      throwError "Audit imports a forbidden goal-placeholder module: {owner}"
  let accepted : List Name := [
    `propext, `Classical.choice, `Quot.sound,
    `KIP126.AdamsSynthetic.hf2AdamsContext_exists,
    `KIP126.StableHomotopy.Spectra.completionModel_exists,
    `KIP126.AdamsSynthetic.standardSyntheticContext,
    `KIP126.AdamsSynthetic.standardAdamsSyntheticComparisons,
    `KIP126.Def.standardSphereApplicability,
    `KIP126.Synthetic.SpectralSequence.CanonicalWeightShift.natural,
    `KIP126.Literature.adamsSyntheticResults,
    `KIP126.Computation.adamsComputations]
  let axioms ← liftCoreM (collectAxioms target)
  for ax in axioms do
    unless accepted.contains ax || ax == ``sorryAx do
      throwError "Unregistered final proof axiom: {ax}"
  for assumption in [``KIP126.Literature.adamsSyntheticResults, ``KIP126.Computation.adamsComputations] do
    unless axioms.contains assumption do
      throwError "Final proof no longer uses the required delivery: {assumption}"
  let mut pending := #[target]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf owner do continue
    if (`KIP126.Challenge.Final).isPrefixOf name ||
        (`KIP126.Main.Challenge).isPrefixOf owner ||
        (`KIP126.Def.Challenge).isPrefixOf owner then
      throwError "Final proof depends on a goal placeholder: {name}: {owner}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  logInfo m!"Final proof axiom dependencies: {axioms.toList}"
  if axioms.contains ``sorryAx then
    logWarning (m!"Final theorem still depends on sorryAx; this is a transitive " ++
      m!"dependency report, not a completed-proof certificate. Imported theorem " ++
      m!"bodies are hidden; the direct source holes are recorded in metadata/proof-obligations.json.")
  else
    logInfo "Final theorem has no sorryAx dependency"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`Tests).isPrefixOf owner do continue
    let isSourceAxiom := info.isAxiom &&
      getOriginalConstKind? env name == some (ConstantKind.ofConstantInfo info)
    if isSourceAxiom || info.type.hasSorry ||
        (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Consumer test contains a local axiom or hole: {name}"
    checked := checked + 1
  logInfo m!"Consumer declarations checked: {checked}; no local admissions"
