module

import all KIP126.Def.AdamsSynthetic.Coherence
import all KIP126.Def.AdamsSynthetic.Comparisons
import all KIP126.Def.AdamsSynthetic.Compatibility
import all KIP126.Def.AdamsSynthetic.Configuration
import all KIP126.Def.AdamsSynthetic.Context
import all KIP126.Def.AdamsSynthetic.Detection
import all KIP126.Def.AdamsSynthetic.Extension
import all KIP126.Def.AdamsSynthetic.ExtensionLabels
import all KIP126.Def.AdamsSynthetic.ExtensionWitnesses
import all KIP126.Def.AdamsSynthetic.ExtensionZero
import all KIP126.Def.AdamsSynthetic.Families
import all KIP126.Def.AdamsSynthetic.Normalized
import all KIP126.Def.AdamsSynthetic.PageExtensions
import all KIP126.Def.AdamsSynthetic.Quotients
import all KIP126.Def.AdamsSynthetic.Recovery
import all KIP126.Def.AdamsSynthetic.Sphere
import all KIP126.Def.AdamsSynthetic.Suspension
import all KIP126.Def.AdamsSynthetic.System
import all KIP126.Def.AdamsSynthetic.Tower
import all KIP126.Def.AdamsSynthetic.AdamsFiltration
import all KIP126.Def.AdamsSynthetic.Background
import all KIP126.Def.AdamsSynthetic.Realization
import all KIP126.Def.AdamsSynthetic.HomologyExactness
import all KIP126.Def.AdamsSynthetic.Mapping
import all KIP126.Def.AdamsSynthetic.MappingComposition
import all KIP126.Def.AdamsSynthetic.MappingDetection
import all KIP126.Def.AdamsSynthetic.MappingEnrichment
import all KIP126.Def.AdamsSynthetic.ESSShift
import all KIP126.Def.AdamsSynthetic.Enrichment
import all KIP126.Def.AdamsSynthetic.Weight
import all KIP126.Def.AdamsSynthetic.ConsumerOperations
import Lean

/-! Internal trust audit. This module exports nothing. It inspects private
implementation declarations as well as the public interface. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Def.AdamsSynthetic).isPrefixOf mod do continue
    if info.isAxiom then
      throwError "Project axiom declaration: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  logInfo m!"AdamsSynthetic internal trust audit: {checked} declarations; only propext, Classical.choice, Quot.sound permitted"
