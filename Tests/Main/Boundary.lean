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
#check_failure KIP126.Main.Internal.Choice.Completion.normalized_quotient
#check_failure KIP126.Main.Internal.Choice.Completion.u_eta_difference_fifteen

-- Exposing the two original statements does not expose the private partial
-- proofs or turn those weaker reductions into public paper conclusions.
#check_failure KIP126.Main.Paper.Internal.ninth_to_third_stem125_weight132_injective
#check_failure KIP126.Main.Paper.Internal.ninth_stem125_weight132_filtration_eleven_of_third
#check_failure KIP126.Main.Paper.Internal.relation_right_zero_factors
#check_failure KIP126.Main.Paper.Internal.eta_indeterminacy_normalize
#check_failure KIP126.Main.Paper.Internal.zero_source_toda_eta_image
#check_failure KIP126.Main.Paper.Internal.alpha_three_restrict_three_zero
#check_failure KIP126.Main.Paper.Internal.alpha_toda_restrict_three_eta_image
#check_failure KIP126.Main.Paper.Internal.alpha_toda_restrict_three_unique
#check_failure KIP126.Main.Paper.Internal.alpha_toda_detected_iff_restrict_three_zero
#check_failure KIP126.Main.Paper.Internal.any_y_h0_detected
#check_failure KIP126.Main.Paper.Internal.any_y_h0_difference_filtration_fifteen
#check_failure KIP126.Main.Paper.Internal.any_y_h0_difference_lambda_two_zero
#check_failure KIP126.Main.Paper.Internal.any_y_h0_lambda_two_independent
#check_failure KIP126.Main.Paper.Internal.any_y_target_lambda_six_independent
#check_failure KIP126.Main.Paper.Internal.any_y_extension_after_lambda_two

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let exported := env
  for name in #[`KIP126.Main.h6_square_differential_dichotomy_and_criterion,
      `KIP126.Main.h6_sq_permanent, `KIP126.Main.adams_two_line_classification] do
    let some info := exported.find? name
      | throwError "Fixed paper endpoint is not exported: {name}"
    liftTermElabM <| Meta.forallTelescope info.type fun args _ => do
      unless args.isEmpty do
        throwError "Fixed paper endpoint acquired a caller premise: {name}"
  for name in #[`KIP126.Main.any_choice_criterion,
      `KIP126.Main.adams_two_line_known_squares,
      `KIP126.Main.adams_two_line_stem126,
      `KIP126.Main.adams_two_line_classification,
      `KIP126.Main.normalized_quotient,
      `KIP126.Main.lambda_eta_theta_square_independent,
      `KIP126.Main.delta_h6_square_eq_lambda_eta_theta_square,
      `KIP126.Main.eta_extension_detection_choice_equivalence,
      `KIP126.Main.eta_extension_excluded_of_d6_vanishes,
      `KIP126.Main.h6_sq_permanent,
      `KIP126.Main.h6_square_differential_dichotomy_and_criterion,
      `KIP126.Main.theta5_square_nonzero_detection_choice_equivalence,
      `KIP126.Main.theta_square_three_possibilities] do
    let some info := exported.find? name
      | throwError "Missing selected paper result: {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Selected paper result was replaced by a direct placeholder: {name}"

-- Every declaration approved for internalization must be unavailable to ordinary consumers.
#check_failure KIP126.Main.SectionSeven.AlphaOneProperties
#check_failure KIP126.Main.SectionSeven.AnyYH0Extension
#check_failure KIP126.Main.SectionSeven.ClassicalInfinityGenerated
#check_failure KIP126.Main.SectionSeven.FiniteDetected
#check_failure KIP126.Main.SectionSeven.FiniteNonzeroDifferential
#check_failure KIP126.Main.SectionSeven.ModuleTripleToda
#check_failure KIP126.Main.SectionSeven.NuExtension5
#check_failure KIP126.Main.SectionSeven.NuExtension9
#check_failure KIP126.Main.SectionSeven.SphereDetected
#check_failure KIP126.Main.SectionSeven.SymmetricTwoMultipliedIndeterminacy
#check_failure KIP126.Main.SectionSeven.TargetNuDivisible
#check_failure KIP126.Main.SectionSeven.ThetaBMultipliedIndeterminacy
#check_failure KIP126.Main.SectionSeven.detected_target_bottom_lambda_four_nonzero
#check_failure KIP126.Main.SectionSeven.eta_extension_excluded_of_d6_vanishes
#check_failure KIP126.Main.SectionSeven.hopfNu
#check_failure KIP126.Main.SectionSeven.lambda_nu_multiple_bottom_zero
#check_failure KIP126.Main.SectionSeven.module_toda_nonempty
#check_failure KIP126.Main.SectionSeven.module_toda_nonempty_of_alpha
#check_failure KIP126.Main.SectionSeven.multiplied_indeterminacy_of_two_torsion
#check_failure KIP126.Main.SectionSeven.normalized_nu_bottom_zero
#check_failure KIP126.Main.SectionSeven.nuBottom
#check_failure KIP126.Main.SectionSeven.target_divisibility_contradiction
#check_failure KIP126.Main.SectionSeven.target_divisibility_forces_cnu_incoming
#check_failure KIP126.Main.SectionSeven.target_nu_divisible
#check_failure KIP126.Main.conditions_imply_d12
#check_failure KIP126.Main.d12_implies_square_and_eta
#check_failure KIP126.Main.d12_necessary
#check_failure KIP126.Main.d6_vanishes_iff_target_survives_twelve
#check_failure KIP126.Main.delta_h6_square_bx
#check_failure KIP126.Main.h6_square_no_outgoing
#check_failure KIP126.Main.lambda_three_eta_u_difference_filtration_fourteen
#check_failure KIP126.Main.lambda_three_eta_u_eq_lambda_six
#check_failure KIP126.Main.lambda_three_eta_u_filtration_fourteen
#check_failure KIP126.Main.normalized_bx_finite
#check_failure KIP126.Main.h6_square_basis
#check_failure KIP126.Main.h6_square_reaches_seven
#check_failure KIP126.Main.h6_square_survives_three
#check_failure KIP126.Main.lambda_eta_theta_square_mod_lambda_zero
#check_failure KIP126.Main.only_d12_differential_reduction
#check_failure KIP126.Main.permanence_or_d12
#check_failure KIP126.Main.square_and_eta_detection_choice_equivalence
#check_failure KIP126.Main.table1
#check_failure KIP126.Main.target_nonzero
#check_failure KIP126.Main.theta5_square_nonzero_detection_choice_invariant
#check_failure KIP126.Main.theta_square_detection_cases
#check_failure KIP126.Main.u_choice_exists

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
