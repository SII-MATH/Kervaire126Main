module

import KIP126.Main
import Lean

/-! A normal Main import exposes fixed results, not the old delivery
mechanism, source implementations, or private page-calculus helpers. -/

#check_failure KIP126.Challenge2
#check_failure KIP126.Main.Axiom.challenge2
#check_failure KIP126.Main.StageInput.witness
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Classical.Adams.MilnorCooperations
#check_failure KIP126.LinProgram.RawData.lookup
#check_failure KIP126.Main.Internal.permanent_survives_of_no_early_hit
#check_failure KIP126.Main.Internal.nonzero_differential_not_zero
#check_failure KIP126.Main.earlier_zero_at
#check_failure KIP126.Main.sphere_start
#check_failure KIP126.Main.SectionSeven.negativeZeroIso
#check_failure KIP126.Main.SectionSeven.negative_lift_zero_factorization
#check_failure KIP126.Main.SectionSeven.lambda_h0_of_two_torsion

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let exported := env
  for name in #[`KIP126.Main.proposition_7_8, `KIP126.Main.h6_sq_permanent] do
    let some info := exported.find? name
      | throwError "Fixed paper endpoint is not exported: {name}"
    liftTermElabM <| Meta.forallTelescope info.type fun args _ => do
      unless args.isEmpty do
        throwError "Fixed paper endpoint acquired a caller premise: {name}"
  for name in #[`KIP126.Main.proposition_7_8, `KIP126.Main.proposition_7_9,
      `KIP126.Main.h6_sq_permanent, `KIP126.Main.SectionSeven.c3_excludes_c5] do
    let some info := exported.find? name
      | throwError "Missing paper proof assembly: {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Paper proof assembly was replaced by a direct placeholder: {name}"
