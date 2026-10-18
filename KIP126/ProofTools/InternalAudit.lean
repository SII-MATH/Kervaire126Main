module
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.Paper.ExtensionDescent
import all KIP126.ProofTools.Paper.ExtensionIndeterminacy
import all KIP126.ProofTools.Paper.ExtensionEssentialSource
import all KIP126.ProofTools.Paper.ExtensionCrossingDichotomy
import all KIP126.ProofTools.Paper.Crossing
import all KIP126.ProofTools.Paper.SyntheticExtensions.LambdaRho
import all KIP126.ProofTools.Paper.SyntheticExtensions
import all KIP126.ProofTools
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.FiniteFiltration
import all KIP126.ProofTools.GeneralizedLeibniz
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDivision
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLift
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.LevelBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL
import all KIP126.ProofTools.GeneralizedLeibniz.LevelZero
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibnizAtLevel
import all KIP126.ProofTools.GeneralizedLeibniz.LevelDivision
import all KIP126.ProofTools.LambdaDivision
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingRange
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.WitnessSquare
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.Survival
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.ProofTools.GeneralizedLeibniz.SphereAutomorphisms
import all KIP126.ProofTools.GeneralizedLeibniz.BoundaryDivision
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedMahowald.HMapCoherence
import all KIP126.ProofTools.GeneralizedMahowald.HTarget
import all KIP126.ProofTools.GeneralizedMahowald.HTargetDetection
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionTarget
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection
import all KIP126.ProofTools.GeneralizedMahowald.ShiftLabels
import all KIP126.ProofTools.GeneralizedMahowald.Synchronization
import all KIP126.ProofTools.GeneralizedMahowald.Geometry
import all KIP126.ProofTools.GeneralizedMahowald.OctahedralPullback
import all KIP126.ProofTools.GeneralizedMahowald.CommonShiftEdge
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerAssembly
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerTarget
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerSpecial
import all KIP126.ProofTools.GeneralizedMahowald.StatementReview
import all KIP126.ProofTools.GeneralizedMahowald.BottomNuInjection
import all KIP126.ProofTools.GeneralizedMahowald.CorrectedTotalTarget
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.ProofTools.GeneralizedMahowald.CommonTotalTarget
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.ProofTools.GeneralizedMahowald.TotalFTransport
import all KIP126.ProofTools.GeneralizedMahowald.CorrectedCoordinates
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeNativeTarget
import all KIP126.ProofTools.GeneralizedMahowald.SourceBoundaryReview
import all KIP126.ProofTools.GeneralizedMahowald.MinimalFinalAssembly
import all KIP126.ProofTools.GeneralizedMahowald.FSourceActual
import all KIP126.ProofTools.GeneralizedMahowald.FSourceRegrade
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.NuCofiberMayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayActual
import all KIP126.ProofTools.GeneralizedMahowald.SphereResidualLabels
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.CommonCoordinates
import all KIP126.ProofTools.GeneralizedMahowald.FSourceTransport
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FTransportLambda
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.MinimalSource
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary
import all KIP126.ProofTools.GeneralizedMahowald.FTransport
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import all KIP126.ProofTools.GeneralizedMahowald.Signs
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.ProofTools.GeneralizedMahowald
import all KIP126.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.ProofTools.GeneralizedMahowald.Detection
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.FinalOperations
import all KIP126.ProofTools.GeneralizedMahowald.KernelCorrection
import all KIP126.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.Language
import all KIP126.ProofTools.Laws
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.Representatives
import all KIP126.ProofTools.Standard
import all KIP126.ProofTools.Stretching
import all KIP126.ProofTools.StretchingRepresentatives


public meta import Checks.Registry
import Lean

/-! Trust audit for article-owned proof and construction responsibilities. Only the exact individually
registered proof/construction holes are permitted; project axioms and synthetic
(elaboration-error) holes are always rejected. SpectralSequence stays sorry-free. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  let expected : Array Json ← entries.filterM fun (row : Json) => do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    pure ((`KIP126.ProofTools).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.ProofTools).isPrefixOf mod do continue
    if info.isAxiom then throwError "Project axiom declaration: {name}"
    let body := info.value? (allowOpaque := true)
    if info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry) then
      throwError "Synthetic sorry from failed elaboration: {name}"
    if info.type.hasSorry || body.any (·.hasSorry) then
      holes := holes.push name.toString
      let some entry := expected.find? (fun e => e.getObjValAs? String "name" == .ok name.toString)
        | throwError "Unregistered proof/construction obligation: {name}"
      let expectedType ← Lean.ofExcept <| entry.getObjValAs? String "type_fingerprint"
      let expectedBody ← Lean.ofExcept <| entry.getObjValAs? String "body_fingerprint"
      unless expectedType == toString (hash (toString info.type)) &&
          expectedBody == toString (hash (toString body)) do
        throwError "Registered obligation changed; review its exact type/body: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  unless holes.qsort (· < ·) == expectedNames.qsort (· < ·) do
    throwError "Proof obligation registry has stale or missing declarations: {holes}"
  let originalGapDeclarations := #[
    "KIP126.ProofTools.Standard.generalizedLeibniz",
    "KIP126.ProofTools.Standard.generalizedMahowald"]
  unless holes.qsort (· < ·) == originalGapDeclarations.qsort (· < ·) do
    throwError "ProofTools permits only the remaining GL1/GL2 and MH2 declarations: {holes}"
  -- These completed tools may use fixed upstream obligations, but must not
  -- depend on either unfinished local paper theorem. In particular, the
  -- general MH1 boundary lift cannot silently use MH2 or generalizedLeibniz.
  let provedTools := #[
    `KIP126.ProofTools.Standard.finitePageExtensionStretching,
    `KIP126.ProofTools.Standard.generalizedLeibnizAtLevel,
    `KIP126.ProofTools.Standard.finiteExtensionAtLevelZero,
    `KIP126.ProofTools.Standard.finiteLambdaDivision,
    `KIP126.ProofTools.Internal.Leibniz.tower_image_filtration_of_kernel_no_crossing,
    `KIP126.ProofTools.Internal.Leibniz.finite_essential_division_of_kernel_no_crossing,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_detects,
    `KIP126.ProofTools.Internal.Mahowald.selected_boundary_nonadjacent,
    `KIP126.ProofTools.Internal.Mahowald.selected_mahowald_case,
    `KIP126.ProofTools.Internal.Leibniz.absoluteBoundary_natural,
    `KIP126.ProofTools.Internal.Leibniz.square_frames,
    `KIP126.ProofTools.Internal.Leibniz.absolute_boundary_square_detects_unshifted,
    `KIP126.ProofTools.Internal.Leibniz.absolute_boundary_square_high_filtration,
    `KIP126.ProofTools.Internal.Leibniz.gl_witness_square_high_filtration,
    `KIP126.ProofTools.Internal.Leibniz.gl_witness_square_detects,
    `KIP126.ProofTools.Internal.Leibniz.gl_left_edge,
    `KIP126.ProofTools.Internal.Leibniz.minimal_length_bottom_tower_no_crossing,
    `KIP126.ProofTools.Internal.Leibniz.differential_absolute_boundary_level,
    `KIP126.ProofTools.Internal.Leibniz.level_gl_left_edge,
    `KIP126.ProofTools.Internal.Leibniz.generalizedLeibniz_at_level,
    `KIP126.ProofTools.Internal.Leibniz.level_finite_extension_of_zero,
    `KIP126.ProofTools.Internal.Leibniz.gl_bottom_target_representative,
    `KIP126.ProofTools.Internal.Leibniz.tower_extension_map,
    `KIP126.ProofTools.Internal.Leibniz.tower_essential_of_mapped_extension,
    `KIP126.ProofTools.Internal.Leibniz.tower_essential_of_mapped_source,
    `KIP126.ProofTools.Internal.Leibniz.normalized_finite_source_image_division,
    `KIP126.ProofTools.Internal.Leibniz.finiteLambdaInfinity,
    `KIP126.ProofTools.Internal.Leibniz.finite_lambda_infinity_nu_heq,
    `KIP126.ProofTools.Internal.Leibniz.finite_lambda_infinity_nonzero_iff_boundary,
    `KIP126.ProofTools.Internal.Leibniz.finite_extension_essential_of_lambda_source,
    `KIP126.ProofTools.Internal.Leibniz.finite_weight_label_heq,
    `KIP126.ProofTools.Internal.Leibniz.finite_witness_lambda_target_nonzero_iff,
    `KIP126.ProofTools.Internal.Leibniz.finite_crossing_of_lifted_witness,
    `KIP126.ProofTools.Internal.Leibniz.finite_witness_of_filtered_source_image,
    `KIP126.ProofTools.Internal.Leibniz.finite_weighted_lambda_high_iff_boundary,
    `KIP126.ProofTools.Internal.Leibniz.nu_lambda_high_iff_boundary,
    `KIP126.ProofTools.Internal.CrossingLabels.lambda_nu_label_nonzero,
    `KIP126.ProofTools.Internal.CrossingLabels.lambda_finite_label_nonzero,
    `KIP126.ProofTools.Internal.Leibniz.page_two_tower_no_crossing,
    `KIP126.ProofTools.Internal.Leibniz.differential_absolute_boundary,
    `KIP126.ProofTools.Internal.Leibniz.absolute_boundary_filtration_cycles,
    `KIP126.ProofTools.Internal.Leibniz.boundary_detects_differential,
    `KIP126.ProofTools.Internal.Leibniz.rho_lift_detected_cycles,
    `KIP126.ProofTools.Internal.Leibniz.rho_lift_detects,
    `KIP126.ProofTools.Internal.Leibniz.absolute_boundary_detected_cycles_weighted,
    `KIP126.ProofTools.Internal.Leibniz.gl1_right_edge_survival,
    `KIP126.ProofTools.Internal.Leibniz.extension_lambda_boundary_shift,
    `KIP126.ProofTools.Internal.Leibniz.infinite_extension_lambda_boundary_shift,
    `KIP126.ProofTools.Internal.Leibniz.finite_quotient_lambda_detects,
    `KIP126.ProofTools.Internal.Leibniz.finite_lambda_division_first_label_congruent,
    `KIP126.ProofTools.Internal.Leibniz.boundary_detects_differential_of_source_congruent,
    `KIP126.ProofTools.Internal.Leibniz.finite_detected_source_division_uniform,
    `KIP126.ProofTools.Internal.Leibniz.finite_lambda_division_differential,
    `KIP126.ProofTools.Internal.Leibniz.sphere_automorphism_quotient_projection,
    `KIP126.ProofTools.Internal.Leibniz.divided_boundary_first_quotient,
    `KIP126.ProofTools.Internal.Leibniz.finite_detected_boundary_differential_weighted,
    `KIP126.ProofTools.Internal.Mahowald.infinity_zero_no_incoming,
    `KIP126.ProofTools.Internal.Mahowald.detects_high_infinity_zero,
    `KIP126.ProofTools.Internal.Mahowald.finite_bottom_high_label_zero,
    `KIP126.ProofTools.Internal.Mahowald.finite_positive_extension_map_e2_zero,
    `KIP126.ProofTools.Internal.Mahowald.positive_extension_map_e2_zero,
    `KIP126.ProofTools.Internal.Mahowald.shifted_finite_bottom_high_label_zero,
    `KIP126.ProofTools.Internal.Mahowald.finite_positive_extension_shifted_map_e2_zero,
    `KIP126.ProofTools.Internal.Mahowald.finite_bottom_detects_label_unique,
    `KIP126.ProofTools.Internal.Mahowald.finite_zero_extension_map_e2_target,
    `KIP126.ProofTools.Internal.Mahowald.zero_extension_map_e2_target,
    `KIP126.ProofTools.Internal.Mahowald.zero_extension_map_e2_bottom_target,
    `KIP126.ProofTools.Internal.Mahowald.may_tensor_common_lift,
    `KIP126.ProofTools.Internal.Mahowald.finite_quotient_octahedral_pullback,
    `KIP126.ProofTools.Internal.Mahowald.finite_quotient_octahedral_pullback_desuspended,
    `KIP126.ProofTools.Internal.Mahowald.normalized_octahedral_comparison,
    `KIP126.ProofTools.Internal.Mahowald.octahedral_lift_difference_factor,
    `KIP126.ProofTools.Internal.Mahowald.octahedral_lift_difference_zero_on_boundary,
    `KIP126.ProofTools.Internal.Leibniz.finite_source_division,
    `KIP126.ProofTools.Internal.Leibniz.divided_boundary_filtration_iff,
    `KIP126.ProofTools.Internal.Leibniz.shift_filtration_iff,
    `KIP126.ProofTools.Internal.Leibniz.classical_noCrossing_absolute_boundary,
    `KIP126.ProofTools.Internal.Leibniz.classical_noCrossing_shifted_absolute_boundary,
    `KIP126.ProofTools.Internal.Leibniz.minimal_length_finite_tower_no_crossing,
    `KIP126.ProofTools.Internal.Leibniz.short_finite_crossing_position,
    `KIP126.ProofTools.Internal.Leibniz.tower_no_crossing_of_correction,
    `KIP126.ProofTools.Internal.quotient_shift_exists,
    `KIP126.ProofTools.Internal.Mahowald.quotient_shift_desuspend_restriction,
    `KIP126.ProofTools.Internal.Mahowald.positive_finite_source_unshifted,
    `KIP126.ProofTools.Internal.Mahowald.zero_finite_source_unshifted,
    `KIP126.ProofTools.Internal.Mahowald.select_finite_extension_source,
    `KIP126.ProofTools.Internal.Mahowald.suspension_finite_target_unshifted,
    `KIP126.ProofTools.Internal.Mahowald.suspension_finite_lambda_unshift,
    `KIP126.ProofTools.Internal.Mahowald.suspension_finite_positive_detects,
    `KIP126.ProofTools.Internal.Mahowald.suspension_finite_bottom_detects,
    `KIP126.ProofTools.Internal.Mahowald.suspension_finite_detects,
    `KIP126.ProofTools.Internal.Mahowald.finite_zero_shift_label,
    `KIP126.ProofTools.Internal.Mahowald.finite_zero_shift_detects,
    `KIP126.ProofTools.Internal.Mahowald.relative_boundary_equal_of_no_crossing,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_iso,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_inclusion_shifted,
    `KIP126.ProofTools.Internal.Mahowald.normalized_h_target_representative,
    `KIP126.ProofTools.Internal.Mahowald.normalized_h_target_detects_native,
    `KIP126.ProofTools.Internal.Mahowald.finite_target_rho_bottom_lift,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_raw_cofiber_boundary,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_shifted_cofiber_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_shifted_cofiber_boundary,
    `KIP126.ProofTools.Internal.Mahowald.finite_target_detects_neg,
    `KIP126.ProofTools.Internal.Mahowald.finite_source_detects_neg,
    `KIP126.ProofTools.Internal.Mahowald.quotient_boundary_lift_desuspended,
    `KIP126.ProofTools.Internal.Mahowald.quotient_lift_image_division,
    `KIP126.ProofTools.Internal.Mahowald.quotient_octahedron_fill,
    `KIP126.ProofTools.Internal.Mahowald.normalized_quotient_maps_equal_on_spheres,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unquotiented_boundary_defect,
    `KIP126.ProofTools.Internal.Mahowald.common_shift_residual_factor,
    `KIP126.ProofTools.Internal.Mahowald.quotient_common_desuspended_boundary_defect,
    `KIP126.ProofTools.Internal.Mahowald.sphere_precomp_preserves_filtration,
    `KIP126.ProofTools.Internal.Mahowald.sphere_automorphism_first_finite,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_precomp_sphere,
    `KIP126.ProofTools.Internal.Mahowald.sphere_automorphism_finite_positive_detects,
    `KIP126.ProofTools.Internal.Mahowald.sphere_automorphism_finite_bottom_detects,
    `KIP126.ProofTools.Internal.Mahowald.sphere_automorphism_finite_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unshift_natural_automorphism_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotient_suspension_inclusion_exists,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_edge_factors_finite_lambda,
    `KIP126.ProofTools.Internal.Mahowald.normalized_common_edge_detection,
    `KIP126.ProofTools.Internal.Mahowald.edgeVerticalCancelIso,
    `KIP126.ProofTools.Internal.Mahowald.edge_vertical_cancel_common_shift,
    `KIP126.ProofTools.Internal.Mahowald.commonEdgeTargetIso,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_finite_edge_canonical,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_edge_canonical_factor,
    `KIP126.ProofTools.Internal.Mahowald.edge_double_vertical_shift,
    `KIP126.ProofTools.Internal.Mahowald.verticalCancellationIso,
    `KIP126.ProofTools.Internal.Mahowald.exactSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.canonicalSuspensionComm,
    `KIP126.ProofTools.Internal.Mahowald.canonicalSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.exactSuspensionTransport_tail,
    `KIP126.ProofTools.Internal.Mahowald.exact_of_canonical_transport_detects,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_boundary_exact_transport,
    `KIP126.ProofTools.Internal.Mahowald.quotientClassUnshift,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unshift_normalized_map,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_suspended_source_iso,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_boundary_suspended_f,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_raw_boundary_equation,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_raw_boundary_detects,
    `KIP126.ProofTools.Internal.Mahowald.cumulative_boundary_permanent,
    `KIP126.ProofTools.Internal.Mahowald.cumulative_boundary_hit,
    `KIP126.ProofTools.Internal.Mahowald.lambdaMultiply_zero_of_le,
    `KIP126.ProofTools.Internal.Mahowald.cumulative_boundary_torsion_lift,
    `KIP126.ProofTools.Internal.Mahowald.cumulative_boundary_torsion_lift_unshifted,
    `KIP126.ProofTools.Internal.Mahowald.source_detects_reindex,
    `KIP126.ProofTools.Internal.Mahowald.extension_at_source_of_normalized_source,
    `KIP126.ProofTools.Internal.Mahowald.transfer_finite_source,
    `KIP126.ProofTools.Internal.Mahowald.shift_class_sub,
    `KIP126.ProofTools.Internal.Mahowald.homotopy_regrade_sub,
    `KIP126.ProofTools.Internal.Mahowald.finite_extension_at_source_minimal_positive,
    `KIP126.ProofTools.Internal.Mahowald.finite_extension_at_source_minimal_zero,
    `KIP126.ProofTools.Internal.Mahowald.finite_extension_at_source_minimal,
    `KIP126.ProofTools.Internal.Mahowald.finite_cycle_image_infinity,
    `KIP126.ProofTools.Internal.Mahowald.finite_cycle_image_correction,
    `KIP126.ProofTools.Internal.Mahowald.mh2_actual_defect_correction,
    `KIP126.ProofTools.Internal.Mahowald.positive_extension_postcompose_e2_zero,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_residual_transpose,
    `KIP126.ProofTools.Internal.Mahowald.boundary_transposed_lambda_infinity_zero,
    `KIP126.ProofTools.Internal.Mahowald.differential_target_boundary,
    `KIP126.ProofTools.Internal.Mahowald.zero_length_differential_residual_zero,
    `KIP126.ProofTools.Internal.Mahowald.zero_length_actual_toda_residual_detects_zero,
    `KIP126.ProofTools.Internal.Mahowald.mh2_actual_defect_subtraction,
    `KIP126.ProofTools.Internal.Mahowald.quotient_common_desuspended_boundary_defect_with_transpose,
    `KIP126.ProofTools.Internal.Mahowald.shifted_finite_lambda_class_general,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unshift_finite_lambda,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unshift_finite_lambda_detects,
    `KIP126.ProofTools.Internal.Mahowald.finite_filtered_target_label,
    `KIP126.ProofTools.Internal.Mahowald.finiteWeightedLambdaClass,
    `KIP126.ProofTools.Internal.Mahowald.finite_weighted_lambda_detects,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_target_label_congruent,
    `KIP126.ProofTools.Internal.Mahowald.finiteWeightedLambdaDivisionClass,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_target_label_congruent_uniform,
    `KIP126.ProofTools.Internal.Mahowald.final_f_division_target,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.finite_lambda_add,
    `KIP126.ProofTools.Internal.Mahowald.finite_divided_source_exact_label,
    `KIP126.ProofTools.Internal.Mahowald.finite_detected_source_division_exact,
    `KIP126.ProofTools.Internal.Mahowald.finite_detected_bottom_first,
    `KIP126.ProofTools.Internal.Mahowald.finite_detected_source_division_exact_uniform,
    `KIP126.ProofTools.Internal.Mahowald.finite_target_source_division_exact,
    `KIP126.ProofTools.Internal.Mahowald.vertical_normalized_finite_lambda_class,
    `KIP126.ProofTools.Internal.Mahowald.vertical_normalized_finite_lambda_detects,
    `KIP126.ProofTools.Internal.Mahowald.zeroEdgeQuotientShiftIso,
    `KIP126.ProofTools.Internal.Mahowald.zero_edge_quotient_shift_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.zero_edge_shift_homotopy_class,
    `KIP126.ProofTools.Internal.Mahowald.zero_edge_quotient_source_back,
    `KIP126.ProofTools.Internal.Mahowald.fSourceRawFunctor,
    `KIP126.ProofTools.Internal.Mahowald.fSourceChi,
    `KIP126.ProofTools.Internal.Mahowald.fSourceKappa,
    `KIP126.ProofTools.Internal.Mahowald.fSourceDifference,
    `KIP126.ProofTools.Internal.Mahowald.negativeFunctorAutomorphism,
    `KIP126.ProofTools.Internal.Mahowald.fSourceSignedChi,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_suspended_source_total,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_suspended_source_signed_total,
    `KIP126.ProofTools.Internal.Mahowald.quotient_unshift_two_natural_transports_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotient_two_shifts_on_spheres,
    `KIP126.ProofTools.Internal.Mahowald.double_quotient_unshift_up_to_source_automorphism,
    `KIP126.ProofTools.Internal.Mahowald.normalized_source_double_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotientClassUnshift_shift,
    `KIP126.ProofTools.Internal.Mahowald.shifted_quotient_total_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.commonCofiberTargetIso,
    `KIP126.ProofTools.Internal.Mahowald.common_cofiber_target_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.normalized_common_cofiber_coordinates_exists,
    `KIP126.ProofTools.Internal.Mahowald.common_cofiber_desuspend_eq_shift_cNu,
    `KIP126.ProofTools.Internal.Mahowald.commonEdgeFlattenIso,
    `KIP126.ProofTools.Internal.Mahowald.commonEdgeTargetFlatIso,
    `KIP126.ProofTools.Internal.Mahowald.common_edge_flatten_preimage,
    `KIP126.ProofTools.Internal.Mahowald.shifted_nu_to_shifted_finite_no_return,
    `KIP126.ProofTools.Internal.Mahowald.finite_source_high_target_extensions_equal,
    `KIP126.ProofTools.Internal.Mahowald.sphere_nu_high_target_map_zero,
    `KIP126.ProofTools.Internal.Mahowald.sphere_nu_high_target_extension,
    `KIP126.ProofTools.Internal.Mahowald.detects_zero_of_detects_same_label_zero,
    `KIP126.ProofTools.Internal.Mahowald.sphere_source_actual_edge_correction,
    `KIP126.ProofTools.Internal.Mahowald.actual_raw_residual_flat_detects_zero,
    `KIP126.ProofTools.Internal.Mahowald.actual_extension_source_native_detects,
    `KIP126.ProofTools.Internal.Mahowald.common_bi_susp_inverse,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_geometric_second_image,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_quotient_second_image,
    `KIP126.ProofTools.Internal.Mahowald.normalize_common_edge_source_length,
    `KIP126.ProofTools.Internal.Mahowald.sphere_source_actual_mahowald_second_image,
    `KIP126.ProofTools.Internal.Mahowald.sphere_shifted_nu_high_target_map_zero,
    `KIP126.ProofTools.Internal.Mahowald.shifted_nuCofiber_high_target_map_zero,
    `KIP126.ProofTools.Internal.Mahowald.nuCofiber_high_target_map_zero,
    `KIP126.ProofTools.Internal.Mahowald.nuCofiber_high_target_extension,
    `KIP126.ProofTools.Internal.Mahowald.actual_edge_correction_of_extensions,
    `KIP126.ProofTools.Internal.Mahowald.nuCofiber_source_actual_edge_correction,
    `KIP126.ProofTools.Internal.Mahowald.nu_classical_shift_iso_exists,
    `KIP126.ProofTools.Internal.Mahowald.shifted_classical_nuCofiber_high_target_map_zero,
    `KIP126.ProofTools.Internal.Mahowald.shifted_classical_nuCofiber_high_target_extension,
    `KIP126.ProofTools.Internal.Mahowald.shifted_classical_nuCofiber_source_actual_edge_correction,
    `KIP126.ProofTools.Internal.Leibniz.tower_essential_iff_target_nonzero_of_no_crossing,
    `KIP126.ProofTools.Internal.Leibniz.minimal_length_finite_essential_iff_target_nonzero,
    `KIP126.ProofTools.Internal.Leibniz.short_finite_has_crossing_iff,
    `KIP126.ProofTools.Internal.Leibniz.shifted_finite_first_kernel_filtration,
    `KIP126.ProofTools.Internal.Leibniz.shifted_finite_source_detects_of_first,
    `KIP126.ProofTools.Internal.Leibniz.positive_finite_source_label_exists,
    `KIP126.ProofTools.Internal.Leibniz.zero_finite_source_label_exists,
    `KIP126.ProofTools.Internal.Leibniz.normalized_finite_source_label_exists,
    `KIP126.ProofTools.Internal.Leibniz.e2_regrade_trans,
    `KIP126.ProofTools.Internal.Leibniz.minimal_finite_witness_of_detected_source,
    `KIP126.ProofTools.Internal.Leibniz.minimal_finite_witness_of_source,
    `KIP126.ProofTools.Internal.Leibniz.finite_lambda_target_not_boundary,
    `KIP126.ProofTools.Internal.Leibniz.minimal_finite_witness_essential_of_target_not_boundary,
    `KIP126.ProofTools.Internal.Leibniz.short_crossing_of_lambda_target_not_high,
    `KIP126.ProofTools.Internal.Leibniz.homotopy_regrade_comp,
    `KIP126.ProofTools.Internal.Leibniz.vertical_shift_regrade,
    `KIP126.ProofTools.Internal.Leibniz.short_finite_noCrossing_tower,
    `KIP126.ProofTools.Internal.Leibniz.source_detects_native,
    `KIP126.ProofTools.Internal.Leibniz.finite_extension_at_source_short,
    `KIP126.ProofTools.Internal.Mahowald.quotient_shift_desuspend_as_native_unshift,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_raw_source_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotientShiftAlongIso,
    `KIP126.ProofTools.Internal.Mahowald.quotientShiftAlongIso_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.quotientShiftAlongIso_evaluation,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_actual_source_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.quotient_zero_unshift_up_to_sphere,
    `KIP126.ProofTools.Internal.Mahowald.shifted_finite_bottom_detects_exists,
    `KIP126.ProofTools.Internal.Mahowald.native_bottom_detected_cycles,
    `KIP126.ProofTools.Internal.Mahowald.native_bottom_detected_first_lift,
    `KIP126.ProofTools.Internal.Mahowald.positive_finite_source_refold,
    `KIP126.ProofTools.Internal.Mahowald.zero_finite_source_refold,
    `KIP126.ProofTools.Internal.Mahowald.normalized_finite_source_bottom_refold,
    `KIP126.ProofTools.Internal.Mahowald.minimal_final_extension_of_detected_source,
    `KIP126.ProofTools.Internal.Mahowald.minimal_final_extension_of_native_source,
    `KIP126.ProofTools.Internal.Mahowald.cycle_add_boundary,
    `KIP126.ProofTools.Internal.Mahowald.finite_target_rep_add_boundary,
    `KIP126.ProofTools.Internal.Mahowald.finite_extension_target_add_boundary,
    `KIP126.ProofTools.Internal.Mahowald.suspension_desuspends_add,
    `KIP126.ProofTools.Internal.Mahowald.infinite_source_label_add,
    `KIP126.ProofTools.Internal.Mahowald.positive_extensions_force_boundary_image_zero,
    `KIP126.ProofTools.Internal.Mahowald.nonzero_leading_image_no_positive_extension,
    `KIP126.ProofTools.Internal.Mahowald.nonzero_boundary_image_obstructs_translation,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_differential,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_boundary,
    `KIP126.ProofTools.Internal.Mahowald.sphere_ext_two_thirteen_zero,
    `KIP126.ProofTools.Internal.Mahowald.commonTargetUnshift,
    `KIP126.ProofTools.Internal.Mahowald.common_target_unshift_shift,
    `KIP126.ProofTools.Internal.Mahowald.common_target_shift_unshift,
    `KIP126.ProofTools.Internal.Mahowald.common_target_unshift_sub,
    `KIP126.ProofTools.Internal.Mahowald.common_target_unshift_filtration,
    `KIP126.ProofTools.Internal.Mahowald.common_target_double_vertical_unshift,
    `KIP126.ProofTools.Internal.Mahowald.common_edge_positive_shift_evaluation,
    `KIP126.ProofTools.Internal.Mahowald.common_shift_regrade,
    `KIP126.ProofTools.Internal.Mahowald.common_regrade_trans,
    `KIP126.ProofTools.Internal.Mahowald.common_flat_lambda_unshift,
    `KIP126.ProofTools.Internal.Mahowald.commonCorrectedGeometry,
    `KIP126.ProofTools.Internal.Mahowald.common_corrected_geometry_desuspend,
    `KIP126.ProofTools.Internal.Mahowald.common_correction_preserves_native_rho,
    `KIP126.ProofTools.Internal.Mahowald.native_bottom_detects_of_restriction,
    `KIP126.ProofTools.Internal.Mahowald.common_target_same_detection_transfer,
    `KIP126.ProofTools.Internal.Mahowald.common_desuspended_finite_edge_flat_canonical,
    `KIP126.ProofTools.Internal.Mahowald.normalized_edge_source_native_lift,
    `KIP126.ProofTools.Internal.Mahowald.actual_common_edge_native_detects,
    `KIP126.ProofTools.Internal.Mahowald.corrected_actual_common_edge_native_detects,
    `KIP126.ProofTools.Internal.Mahowald.cancelBiShiftNatIso,
    `KIP126.ProofTools.Internal.Mahowald.cancelBiShiftNatIso_map,
    `KIP126.ProofTools.Internal.Mahowald.totalWeightShiftCancellation,
    `KIP126.ProofTools.Internal.Mahowald.exactTotalSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.canonicalTotalSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_source_iso,
    `KIP126.ProofTools.Internal.Mahowald.normalized_g_boundary_total_f,
    `KIP126.ProofTools.Internal.Mahowald.totalSourceRelabel,
    `KIP126.ProofTools.Internal.Mahowald.totalSourceSignedTransport,
    `KIP126.ProofTools.Internal.Mahowald.canonicalTotalSourceTransport,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_source_signed,
    `KIP126.ProofTools.Internal.Mahowald.normalized_total_source_double_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_raw_boundary_equation,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_actual_source_unshift_detects,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_raw_boundary_detects,
    `KIP126.ProofTools.Internal.Mahowald.rotatedNuRouteTriangle,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_f_exponent,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_g_exponent,
    `KIP126.ProofTools.Internal.Mahowald.suspension_projection_one,
    `KIP126.ProofTools.Internal.Mahowald.map_filtration_one_shift_iff,
    `KIP126.ProofTools.Internal.Mahowald.map_filtration_one_neg_iff,
    `KIP126.ProofTools.Internal.Mahowald.normalized_exponent_neg_shift,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_h_exponent,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_exponent_sum,
    `KIP126.ProofTools.Internal.Mahowald.original_normalized_nu_rotation_distinguished,
    `KIP126.ProofTools.Internal.Mahowald.quotient_one_negative,
    `KIP126.ProofTools.Internal.Mahowald.lambda_one_injective_of_quotient_vanishing,
    `KIP126.ProofTools.Internal.Mahowald.lambda_one_injective_at_diagonal,
    `KIP126.ProofTools.Internal.Mahowald.negative_lift_factorization,
    `KIP126.ProofTools.Internal.Mahowald.lambda_to_positive_zero,
    `KIP126.ProofTools.Internal.Mahowald.normalized_zero_map_form,
    `KIP126.ProofTools.Internal.Mahowald.normalized_zero_map,
    `KIP126.ProofTools.Internal.Mahowald.homology_short_exact_of_boundary_zero,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_boundary_homology_zero,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_homology_short_exact,
    `KIP126.ProofTools.Internal.Mahowald.negative_lift_at_one,
    `KIP126.ProofTools.Internal.Mahowald.negative_lift_at_one_factorization,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_selected_full_lift,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_triangle_lift,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_source_sphere,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_selected_connecting_eq,
    `KIP126.ProofTools.Internal.Mahowald.zero_positive_iso,
    `KIP126.ProofTools.Internal.Mahowald.zero_negative_iso,
    `KIP126.ProofTools.Internal.Mahowald.negative_lift_zero_map_form,
    `KIP126.ProofTools.Internal.Mahowald.raw_normalized_connecting,
    `KIP126.ProofTools.Internal.Mahowald.raw_connecting_zero_zero_one,
    `KIP126.ProofTools.Internal.Mahowald.rotated_normalized_connecting_square,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_normalized_distinguished,
    `KIP126.ProofTools.Internal.Mahowald.desuspend_bijective,
    `KIP126.ProofTools.Internal.Mahowald.desuspend_postcompose,
    `KIP126.ProofTools.Internal.Mahowald.raw_cycles_iff,
    `KIP126.ProofTools.Internal.Mahowald.desuspend_mem_raw_cycles,
    `KIP126.ProofTools.Internal.Mahowald.desuspendFirstPage_bijective,
    `KIP126.ProofTools.Internal.Mahowald.lift_desuspend,
    `KIP126.ProofTools.Internal.Mahowald.lift_desuspend_bijective,
    `KIP126.ProofTools.Internal.Mahowald.lift_desuspend_natural,
    `KIP126.ProofTools.Internal.Mahowald.lift_desuspend_connecting,
    `KIP126.ProofTools.Internal.Mahowald.desuspend_mem_raw_cycles_iff,
    `KIP126.ProofTools.Internal.Mahowald.exists_suspendsClass,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspend_bijective,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspend_postcompose,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspendHom,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspendHom_bijective,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspendHom_zero,
    `KIP126.ProofTools.Internal.Mahowald.boundary_desuspendHom_natural,
    `KIP126.ProofTools.Internal.Mahowald.raw_boundaries_iff,
    `KIP126.ProofTools.Internal.Mahowald.desuspend_mem_raw_boundaries_iff,
    `KIP126.ProofTools.Internal.Mahowald.initial_class_boundary_iff,
    `KIP126.ProofTools.Internal.Mahowald.class_boundary_iff,
    `KIP126.ProofTools.Internal.Mahowald.desuspendsClass_boundary_iff,
    `KIP126.ProofTools.Internal.Mahowald.desuspendsClass_eq_zero_iff,
    `KIP126.ProofTools.Internal.Mahowald.desuspendsClass_ne_zero_iff,
    `KIP126.ProofTools.Internal.Mahowald.suspension_desuspends_sub,
    `KIP126.ProofTools.Internal.Mahowald.desuspendsClass_eq_iff,
    `KIP126.ProofTools.Internal.Mahowald.exists_suspendsClass_mem_boundary,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_suspends,
    `KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_suspends_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.commonRawSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.commonTotalSuspensionTransport,
    `KIP126.ProofTools.Internal.Mahowald.common_edge_flat_iso_factor,
    `KIP126.ProofTools.Internal.Mahowald.commonTotalQuotientIso,
    `KIP126.ProofTools.Internal.Mahowald.common_total_quotient_inclusion,
    `KIP126.ProofTools.Internal.Mahowald.double_pure_unshift_up_to_source_automorphism,
    `KIP126.ProofTools.Internal.Mahowald.common_total_quotient_sphere_equation,
    `KIP126.ProofTools.Internal.Mahowald.common_total_native_detection,
    `KIP126.ProofTools.Internal.Mahowald.unit_first_quotient_11_13_zero,
    `KIP126.ProofTools.Internal.Mahowald.balanced_four_first_quotient_15_17_zero,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_source_ext_zero,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_no_crossing,
    `KIP126.ProofTools.Internal.Mahowald.regradeE2_zero,
    `KIP126.ProofTools.Internal.Mahowald.target_nu_label_zero,
    `KIP126.ProofTools.Internal.Mahowald.zero_finite_extension_witness,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_g_zero_witness,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_h_zero_witness,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_g_zero_extension,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_h_boundary_witness,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_h_boundary_extension,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_remaining_premises,
    `KIP126.ProofTools.Internal.Mahowald.common_corrected_geometry_second_image,
    `KIP126.ProofTools.Internal.Mahowald.common_corrected_total_native_detection,
    `KIP126.ProofTools.Internal.Mahowald.specific_top_lambda_injective,
    `KIP126.ProofTools.Internal.Mahowald.sphere_ext_three_fourteen_zero,
    `KIP126.ProofTools.Internal.Mahowald.sphere_nu_infinity_zero_of_ambient_zero,
    `KIP126.ProofTools.Internal.Mahowald.nuSphere_pi_11_13_filtration_four,
    `KIP126.ProofTools.Internal.Mahowald.specific_source_to_first_quotient_zero,
    `KIP126.ProofTools.Internal.Mahowald.specific_two_cell_first_quotient_injective,
    `KIP126.ProofTools.Internal.Mahowald.nu_triangle_bottom_boundary_image_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.nu_bottom_boundary_first_quotient_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.nu_bottom_boundary_leading_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.zero_normalized_leading_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.candidate_zero_differential,
    `KIP126.ProofTools.Internal.Mahowald.mh2_candidate_refutation_of_bottom_nonzero,
    `KIP126.ProofTools.Internal.Mahowald.rotated_nu_generalized_mahowald_law_false,
    `KIP126.ProofTools.Internal.Mahowald.quotient_shift_desuspend_as_unshift,
    `KIP126.ProofTools.Internal.Mahowald.native_bottom_detects_of_same_restriction,
    `KIP126.ProofTools.Internal.Mahowald.corrected_native_bottom_detects,
    `KIP126.ProofTools.Internal.Mahowald.normalized_f_total_raw_boundary_detects_transport,
    `KIP126.ProofTools.Internal.Mahowald.quotient_class_unshift_regrade_source,
    `KIP126.ProofTools.Internal.Mahowald.homotopy_regrade_self,
    `KIP126.ProofTools.Internal.Mahowald.finite_e2_regrade_roundtrip,
    `KIP126.ProofTools.Internal.Mahowald.minimal_corrected_total_extension,
    `KIP126.ProofTools.Internal.Mahowald.normalized_included_source_label,
    `KIP126.ProofTools.Internal.Mahowald.corrected_second_image_finite_label,
    `KIP126.ProofTools.Internal.Mahowald.finite_edge_detection_source_length,
    `KIP126.ProofTools.Internal.Mahowald.finite_native_bottom_detection_reindex_exists,
    `KIP126.ProofTools.Internal.Mahowald.zero_level_native_detection,
    `KIP126.ProofTools.Internal.Mahowald.ZeroLayerDetectedPair,
    `KIP126.ProofTools.Internal.Mahowald.generalized_mahowald_zero_layer_sphere,
    `KIP126.ProofTools.Internal.Mahowald.main_nu_mahowald_zero_layer,
    `KIP126.ProofTools.Standard.nuCofiberMahowaldZeroLayer,
    `KIP126.ProofTools.Paper.finiteExtensionCorrectionLabel,
    `KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter,
    `KIP126.ProofTools.Paper.FiniteExtensionNonliftableShortTo,
    `KIP126.ProofTools.Paper.finiteExtension_nonliftableShort_or_lateCrossing]
  let mut pending : Array Name := #[]
  -- Main checks its ordinary-import dependency frontier against this same ledger.
  -- Here import-all restores ProofTools proof bodies, so these roots receive the
  -- full recursive no-local-gap check alongside the completed private helpers.
  let rewire ← Lean.ofExcept <| ledger.getObjVal? "main_zero_layer_rewire_2026_10_16"
  let mainBoundary ← Lean.ofExcept <|
    rewire.getObjValAs? (Array String) "proofTools_boundary_declarations"
  unless !mainBoundary.isEmpty do
    throwError "Main-to-ProofTools dependency frontier must not be empty"
  let mut boundaryNames : NameSet := {}
  for sourceName in mainBoundary do
    let name := sourceName.toName
    if isPrivateName name then
      throwError "Main dependency frontier contains a private ProofTools declaration: {name}"
    if boundaryNames.contains name then
      throwError "Duplicate Main-to-ProofTools boundary declaration: {name}"
    boundaryNames := boundaryNames.insert name
    let some _ := env.find? name
      | throwError "Missing Main-to-ProofTools boundary declaration: {name}"
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing module for Main-to-ProofTools boundary declaration: {name}"
    unless (`KIP126.ProofTools).isPrefixOf env.header.moduleNames[idx.toNat]! do
      throwError "Main dependency frontier contains a declaration outside ProofTools: {name}"
    pending := pending.push name
  for sourceName in provedTools do
    let some (name, _) := env.constants.toList.find? (fun (name, _) =>
        ((privateToUserName? name).getD name) == sourceName)
      | throwError "Missing completed tool: {sourceName}"
    pending := pending.push name
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing proof dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf mod do continue
    let body := info.value? (allowOpaque := true)
    if (`KIP126.ProofTools).isPrefixOf mod &&
        (info.type.hasSorry || body.any (·.hasSorry)) then
      throwError "Completed tool depends on a local paper proof gap: {name}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := body then pending := pending ++ value.getUsedConstants
  logInfo m!"ProofTools Main dependency boundary audit: {mainBoundary.size} roots have no local paper proof gaps"
  logInfo m!"ProofTools trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
