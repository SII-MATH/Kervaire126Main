module

import all KIP126.Def.Literature.Applicability
import all KIP126.Def.Literature.BHS
import all KIP126.Def.Literature.BX
import all KIP126.Def.Literature.Classical
import all KIP126.Def.Literature.ClassicalRange
import all KIP126.Def.Literature.Delivery
import all KIP126.Def.Literature.EInfinity
import all KIP126.Def.Literature.Lift
import all KIP126.Def.Literature.May
import all KIP126.Def.Literature.Moss
import all KIP126.Def.Literature.Rigidity
import all KIP126.Def.Literature.RealizationTransport
import all KIP126.Def.Literature.Secondary
import all KIP126.Def.Literature.Toda
import all KIP126.Def.Literature.Triangles
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
    unless (`KIP126.Def.Literature).isPrefixOf mod do continue
    if info.isAxiom then
      throwError "Project axiom declaration: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  logInfo m!"Literature internal trust audit: {checked} declarations; only propext, Classical.choice, Quot.sound permitted"
