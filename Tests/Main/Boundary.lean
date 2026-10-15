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

#check_failure KIP126.Main.Internal.High125.detector_injective_filtration15
#check_failure KIP126.Main.Internal.NuFifth.nu_five_of_three
#check_failure KIP126.Main.Internal.AlphaOne.alpha_one_exists
#check_failure KIP126.Main.SectionSeven.Internal.nu_target_full_of_nonzero
#check_failure KIP126.Main.SectionSeven.Internal.main_weak_high_representative
#check_failure KIP126.Main.sphere_filtration_lambda
#check_failure KIP126.Main.lambda_three_eta_u_difference_filtration_fifteen

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let exported := env
  for name in #[`KIP126.Main.h6_square_differential_dichotomy_and_criterion, `KIP126.Main.h6_sq_permanent] do
    let some info := exported.find? name
      | throwError "Fixed paper endpoint is not exported: {name}"
    liftTermElabM <| Meta.forallTelescope info.type fun args _ => do
      unless args.isEmpty do
        throwError "Fixed paper endpoint acquired a caller premise: {name}"
  for name in #[`KIP126.Main.h6_square_differential_dichotomy_and_criterion, `KIP126.Main.eta_extension_excluded_of_d6_vanishes,
      `KIP126.Main.h6_sq_permanent, `KIP126.Main.SectionSeven.eta_extension_excluded_of_d6_vanishes,
      `KIP126.Main.theta5_square_nonzero_detection_choice_invariant,
      `KIP126.Main.permanence_or_d12,
      `KIP126.Main.d12_implies_square_and_eta,
      `KIP126.Main.conditions_imply_d12,
      `KIP126.Main.SectionSeven.detected_target_bottom_lambda_four_nonzero,
      `KIP126.Main.SectionSeven.target_nu_divisible,
      `KIP126.Main.u_choice_exists,
      `KIP126.Main.lambda_three_eta_u_filtration_fourteen,
      `KIP126.Main.lambda_three_eta_u_eq_lambda_six,
      `KIP126.Main.lambda_three_eta_u_difference_filtration_fourteen,
      `KIP126.Main.theta_square_detection_cases,
      `KIP126.Main.theta_square_three_possibilities,
      `KIP126.Main.table1,
      `KIP126.Main.delta_h6_square_bx,
      `KIP126.Main.delta_h6_square_eq_lambda_eta_theta_square] do
    let some info := exported.find? name
      | throwError "Missing paper proof assembly: {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Paper proof assembly was replaced by a direct placeholder: {name}"

-- The mathematical names replace the historical paper-number predicates.
#check_failure KIP126.Main.D12
#check_failure KIP126.Main.C3
#check_failure KIP126.Main.C4At
#check_failure KIP126.Main.C4
#check_failure KIP126.Main.C5At
#check_failure KIP126.Main.C5
#check_failure KIP126.Main.proposition_7_8
#check_failure KIP126.Main.proposition_7_9
#check_failure KIP126.Main.SectionSeven.c3_excludes_c5
#check_failure KIP126.Main.c4_c5_choice_equivalence
