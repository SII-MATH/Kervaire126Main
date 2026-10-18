module

import KIP126.Literature
import Lean

open KIP126.Literature.Geometry KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

example (n : ℕ) : KervaireInvariantOneExists n ↔
    ∃ j : ℕ, 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧
      NonzeroSurvival model.classical.sphere (2, ((2 ^ (j + 1) : ℕ) : ℤ))
        (model.standardClasses.standardHiSquare j) := browder_iff n

-- The dimension convention itself excludes 0; Browder is not needed.
example : ¬ KervaireInvariantOneExists 0 := by
  rintro ⟨k, hk, _⟩
  omega

-- Neither the geometric definitions nor Browder consume the later result.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Geometry).isPrefixOf mod then
      throwError "Geometric literature imported its downstream result: {mod}"
  -- The private analysis imports must not change the integer-order instance
  -- expression that occurs in the older frozen filtered-group interfaces.
  let order ← liftTermElabM <| Meta.synthInstance
    (mkApp (mkConst ``Preorder [Level.zero]) (mkConst ``Int))
  if order.getUsedConstants.contains `Int.instConditionallyCompleteLinearOrder then
    throwError "Geometry leaked an analytic integer-order instance into Literature consumers"
