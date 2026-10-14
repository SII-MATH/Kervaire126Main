module

import all KIP126.Def.Computation.Basis
import all KIP126.Def.Computation.Classes
import all KIP126.Def.Computation.Cofiber
import all KIP126.Def.Computation.Delivery
import all KIP126.Def.Computation.Near126
import all KIP126.Def.Computation.Route
import all KIP126.Def.Computation.Source
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
    unless (`KIP126.Def.Computation).isPrefixOf mod do continue
    if info.isAxiom then
      throwError "Project axiom declaration: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  logInfo m!"Computation internal trust audit: {checked} declarations; only propext, Classical.choice, Quot.sound permitted"
