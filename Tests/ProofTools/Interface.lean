module

public import KIP126.ProofTools
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

-- A normal consumer imports only the public entry point. The contract locks
-- complete types, universe parameters, exports and transitive axiom dependencies.
-- Direct sorry obligations are locked separately by the internal trust audits.
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../interface/baselines/proof-tools-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let declarations := named ++ generated
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.SpectralSequence).isPrefixOf mod &&
        !(`KIP126.AdamsSynthetic).isPrefixOf mod &&
        !(`KIP126.Literature).isPrefixOf mod &&
        !(`KIP126.E2Computation).isPrefixOf mod &&
        !(`KIP126.ProofTools).isPrefixOf mod then
      throwError "ProofTools crossed its dependency boundary: {mod}"
  for decl in declarations do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing public interface: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "Public type or universe parameters changed: {name}"
    let expectedAxioms ← ofExcept <| decl.getObjValAs? (Array String) "axioms"
    let actualAxioms ← collectAxioms name.toName
    unless (actualAxioms.map Name.toString).qsort (· < ·) == expectedAxioms.qsort (· < ·) do
      throwError "Public trust dependencies changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.ProofTools).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    if (`KIP126.ProofTools.Operations).isPrefixOf name then
      throwError "Redundant operation facade was reintroduced: {name}"
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    let added := actualExports.filter (!expectedExports.contains ·)
    let missing := expectedExports.filter (!actualExports.contains ·)
    throwError "Public exports changed; added: {added}; missing: {missing}"

-- Prespectrum, concrete towers, Milnor/cobar and program rows are not part
-- of this ordinary consumer import.
#check_failure KIP126.StableHomotopy.Implementation.FoundationInput
#check_failure KIP126.Classical.Adams.MilnorCooperations
#check_failure KIP126.Core.SpectralSequence.FilteredComplex
#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso

#check_failure KIP126.Main.Axiom.challenge2
#check_failure KIP126.LinProgram.RawData.lookup

-- A source result package must never become an ordinary downstream premise.
#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results

run_cmd do
  let env ← getEnv
  let exported := env.setExporting true
  for (name, info) in env.constants.toList do
    unless (`KIP126.ProofTools.Standard).isPrefixOf name ||
        name == `KIP126.ProofTools.Internal.Mahowald.main_nu_mahowald_zero_layer do continue
    unless (exported.find? name).isSome do continue
    liftTermElabM <| Meta.forallTelescope info.type fun args _ => do
      for arg in args do
        let ty ← Meta.inferType arg
        for dep in ty.getUsedConstants do
          if dep == `KIP126.Kervaire.Route.Model ||
              dep == `KIP126.Kervaire.Route.ModelData ||
              dep == `KIP126.Literature.LiteratureInterface ||
              dep == `KIP126.Literature.LiteratureResults ||
              dep == `KIP126.Computation.ComputationInterface ||
              dep == `KIP126.Computation.RouteResults ||
              dep == `KIP126.Computation.Near126Results then
            throwError "Fixed public interface asks its caller for an upstream result package: {name}"

#check_failure KIP126.ProofTools.Standard.lambda_target_class
#check_failure KIP126.ProofTools.Internal.finite_representatives_lift
#check_failure KIP126.ProofTools.Operations.grade_difference
#check_failure KIP126.ProofTools.Internal.Mahowald.actual_rho_kernel_correction

#check_failure KIP126.ProofTools.Internal.Mahowald.finite_lambda_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.selected_mahowald_case

#check_failure KIP126.ProofTools.Internal.Leibniz.square_frames
#check_failure KIP126.ProofTools.Internal.Leibniz.generalizedLeibniz_at_level
#check_failure KIP126.ProofTools.Internal.Leibniz.LevelFiniteExtensionWitness
#check_failure KIP126.ProofTools.Internal.Leibniz.level_finite_extension_of_zero
#check_failure KIP126.ProofTools.Internal.Leibniz.TowerKernelNoCrossing
#check_failure KIP126.ProofTools.Internal.Leibniz.normalized_finite_division_of_kernel_no_crossing
#check_failure KIP126.ProofTools.Internal.Leibniz.finite_essential_division_of_kernel_no_crossing
#check_failure KIP126.ProofTools.Internal.Leibniz.absolute_boundary_square_detects_unshifted
#check_failure KIP126.ProofTools.Internal.Leibniz.absolute_boundary_square_high_filtration
#check_failure KIP126.ProofTools.Internal.Leibniz.gl_witness_square_high_filtration
#check_failure KIP126.ProofTools.Internal.Leibniz.gl_witness_square_detects
#check_failure KIP126.ProofTools.Internal.Leibniz.gl_bottom_target_representative
#check_failure KIP126.ProofTools.Internal.Leibniz.lambdaRawInfinity_nu_representative
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_quotient_octahedral_pullback
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_quotient_octahedral_pullback_desuspended
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_octahedral_comparison
#check_failure KIP126.ProofTools.Internal.Mahowald.octahedral_lift_difference_factor
#check_failure KIP126.ProofTools.Internal.Mahowald.octahedral_lift_difference_zero_on_boundary
#check_failure KIP126.ProofTools.Internal.CrossingLabels.lambda_nu_label_nonzero
#check_failure KIP126.ProofTools.Internal.Leibniz.differential_absolute_boundary
#check_failure KIP126.ProofTools.Internal.Leibniz.page_two_tower_no_crossing
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_boundary_lift_desuspended
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_target_detects_neg

#check_failure KIP126.ProofTools.Internal.Leibniz.absolute_boundary_filtration_cycles
#check_failure KIP126.ProofTools.Internal.Leibniz.boundary_detects_differential
#check_failure KIP126.ProofTools.Internal.Leibniz.finite_source_division
#check_failure KIP126.ProofTools.Internal.Leibniz.divided_boundary_filtration_iff
#check_failure KIP126.ProofTools.Internal.Leibniz.shift_filtration_iff
#check_failure KIP126.ProofTools.Internal.Leibniz.classical_noCrossing_absolute_boundary
#check_failure KIP126.ProofTools.Internal.Leibniz.classical_noCrossing_shifted_absolute_boundary
#check_failure KIP126.ProofTools.Internal.Leibniz.minimal_length_finite_tower_no_crossing
#check_failure KIP126.ProofTools.Internal.Leibniz.short_finite_crossing_position
#check_failure KIP126.ProofTools.Internal.Leibniz.tower_no_crossing_of_correction
#check_failure KIP126.ProofTools.Internal.quotient_shift_exists
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_shift_desuspend_restriction
#check_failure KIP126.ProofTools.Internal.Mahowald.relative_boundary_equal_of_no_crossing
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_iso
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_g_shifted_cofiber_inclusion
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_g_shifted_cofiber_boundary

#check_failure KIP126.ProofTools.Internal.Leibniz.rho_lift_detected_cycles
#check_failure KIP126.ProofTools.Internal.Leibniz.gl1_right_edge_survival
#check_failure KIP126.ProofTools.Internal.Mahowald.may_tensor_common_lift
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_common_desuspended_boundary_defect
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_unshift_natural_automorphism_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.common_desuspended_edge_canonical_factor
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_f_raw_boundary_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.cumulative_boundary_torsion_lift
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_extension_at_source_minimal
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_target_source_division_exact
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_common_desuspended_boundary_defect_with_transpose
#check_failure KIP126.ProofTools.Internal.Mahowald.quotient_unshift_finite_lambda_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_source_double_unshift_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.shifted_quotient_total_unshift_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.sphere_source_actual_edge_correction
#check_failure KIP126.ProofTools.Internal.Mahowald.common_cofiber_desuspend_eq_shift_cNu
#check_failure KIP126.ProofTools.Internal.Leibniz.finite_extension_at_source_short
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_f_raw_source_unshift_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.sphere_source_actual_mahowald_second_image
#check_failure KIP126.ProofTools.Internal.Mahowald.shifted_classical_nuCofiber_source_actual_edge_correction

#check_failure KIP126.ProofTools.Internal.Leibniz.finite_lambda_division_first_label_congruent

#check_failure KIP126.ProofTools.Internal.Leibniz.extension_lambda_boundary_shift
#check_failure KIP126.ProofTools.Internal.Leibniz.infinite_extension_lambda_boundary_shift

#check_failure KIP126.ProofTools.Internal.Leibniz.boundary_detects_differential_of_source_congruent

#check_failure KIP126.ProofTools.Internal.Leibniz.rho_lift_detects
#check_failure KIP126.ProofTools.Internal.Leibniz.finite_detected_source_division_uniform
#check_failure KIP126.ProofTools.Internal.Leibniz.finite_lambda_division_differential
#check_failure KIP126.ProofTools.Internal.Leibniz.sphere_automorphism_quotient_projection
#check_failure KIP126.ProofTools.Internal.Leibniz.divided_boundary_first_quotient

#check_failure KIP126.ProofTools.Internal.Leibniz.finite_detected_boundary_differential_weighted

-- The first-quotient compatibility consumers remain private implementation.
#check_failure KIP126.ProofTools.Internal.Mahowald.quotientUnshift
#check_failure KIP126.ProofTools.Internal.Mahowald.positive_finite_source_unshifted
#check_failure KIP126.ProofTools.Internal.Mahowald.zero_finite_source_unshifted
#check_failure KIP126.ProofTools.Internal.Mahowald.suspension_finite_target_unshifted
#check_failure KIP126.ProofTools.Internal.Mahowald.FiniteExtensionAtSource
#check_failure KIP126.ProofTools.Internal.Mahowald.select_finite_extension_source
#check_failure KIP126.ProofTools.Internal.Mahowald.suspension_finite_lambda_unshift
#check_failure KIP126.ProofTools.Internal.Mahowald.suspension_finite_positive_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.suspension_finite_detects
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_inclusion
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_g_cofiber_inclusion_shifted
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_h_target_representative
#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_h_target_detects_native
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_target_rho_bottom_lift

#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_finite_source_bottom_refold
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_extension_target_add_boundary
#check_failure KIP126.ProofTools.Internal.Mahowald.nonzero_leading_image_no_positive_extension

#check_failure KIP126.ProofTools.Internal.Mahowald.common_flat_lambda_unshift

#check_failure KIP126.ProofTools.Internal.Mahowald.common_correction_preserves_native_rho

#check_failure KIP126.ProofTools.Internal.Mahowald.corrected_actual_common_edge_native_detects

#check_failure KIP126.ProofTools.Internal.Mahowald.normalized_f_total_raw_boundary_detects

#check_failure KIP126.ProofTools.Internal.Mahowald.rotated_nu_normalized_distinguished

#check_failure KIP126.ProofTools.Internal.Mahowald.mh2BoundaryClass_suspends_nonzero
#check_failure KIP126.ProofTools.Internal.Mahowald.common_total_native_detection

#check_failure KIP126.ProofTools.Internal.Mahowald.rotated_nu_remaining_premises

#check_failure KIP126.ProofTools.Internal.Mahowald.common_corrected_total_native_detection

#check_failure KIP126.ProofTools.Internal.Mahowald.nu_bottom_boundary_leading_nonzero

#check_failure KIP126.ProofTools.Internal.Mahowald.rotated_nu_generalized_mahowald_law_false

#check_failure KIP126.ProofTools.Internal.Mahowald.minimal_corrected_total_extension

-- The only new public bridge is the exact zero-layer nu-cofiber instance.
-- Its representative construction and generic zero-layer proof stay private.
#check_failure KIP126.ProofTools.Internal.Mahowald.generalized_mahowald_zero_layer_sphere
#check_failure KIP126.ProofTools.Standard.nuCofiberMahowaldZeroLayer
#check_failure KIP126.ProofTools.Internal.Mahowald.finite_level_extension_of_common_representative
#check_failure KIP126.ProofTools.classical_lift_obstruction_iff

section NuCofiberZeroLayerConsumer
open CategoryTheory KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.ProofTools
open KIP126.AdamsSynthetic.Standard (model)

example
    (x : Ambient model (.shift 3 .sphere) (8,133))
    (y : Ambient model .sphere (11,136))
    (xBar : Ambient model .nuCofiber (8,134))
    (yBar : Ambient model .nuCofiber (11,136))
    (suspendedX : Ambient model (.shift 1 (.shift 3 .sphere)) (8,134))
    (hx : IsCycle model (.shift 3 .sphere) 2 (8,133) x)
    (hy : IsCycle model .sphere 1 (11,136) y)
    (hxBar : IsCycle model .nuCofiber 2 (8,134) xBar)
    (hyBar : IsPermanent model .nuCofiber (11,136) yBar)
    (hsusp : (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass
      8 134 suspendedX x)
    (hh : FiniteExtension model .nuCofiber (.shift 1 (.shift 3 .sphere))
      (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 0 8 134 xBar suspendedX)
    (hd : DifferentialAt model .nuCofiber 3 (8,134) (11,136) xBar yBar)
    (hcross : FiniteNoCrossing model .nuCofiber (.shift 1 (.shift 3 .sphere))
        (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 0 8 134 ∨
      NoCrossingOn model .nuCofiber 3 3 (8,134))
    (hg : FiniteExtension model .sphere .nuCofiber
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 0 11 136 y yBar) :
    IsCycle model (.shift 3 .sphere) 3 (8,133) x ∧
      ∃ y' : Ambient model .sphere (11,136),
        FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
          4 3 8 133 x y' ∧ Congruent model .sphere 3 (11,136) y' y := by
  exact KIP126.ProofTools.Internal.Mahowald.main_nu_mahowald_zero_layer
    x y xBar yBar suspendedX hx hy hxBar hyBar hsusp hh hd hcross hg

end NuCofiberZeroLayerConsumer
