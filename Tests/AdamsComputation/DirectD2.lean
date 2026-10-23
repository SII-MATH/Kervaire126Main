module

import KIP126.AdamsComputation
import Lean

/-! Direct Adams d₂ certification is consumable before SS propagation and the
operation rules. Nonzero named classes use the same fixed sphere and E₂ basis. -/
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic.Standard
open KIP126.Computation.Table KIP126.Computation.Standard

example : HasNonzeroDifferential model.classical.sphere 2 (7,70) (9,71)
    (product h0Six h6) (product h0 (atom .b)) := d2_h0Six_h6

example : Statement
    ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2], "S0_AdamsE2_basis/d2", 2855⟩ :=
  direct_d2_result _ (List.mem_of_getElem? (i := 1) (by rfl))

example : Statement
    ⟨.sphere, .equation, 2, 11, 137, [0], 13, 138, [3], "S0_AdamsE2_basis/d2", 2923⟩ :=
  direct_d2_result _ (List.mem_of_getElem? (i := 2) (by rfl))

example : Statement
    ⟨.sphere, .equation, 2, 11, 137, [3], 13, 138, [4], "S0_AdamsE2_basis/d2", 2926⟩ :=
  direct_d2_result _ (List.mem_of_getElem? (i := 3) (by rfl))

#check_failure KIP126.Computation.Table.result
#check_failure KIP126.Computation.Table.Raw.claims
#check_failure KIP126.Computation.Standard.d2_x125_8

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if #[`KIP126.ProofTools, `KIP126.SSComputation, `KIP126.Main,
        `KIP126.Geometry].any (·.isPrefixOf mod) then
      throwError "Direct Adams d2 consumer imported a downstream module: {mod}"
