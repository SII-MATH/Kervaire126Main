module
import all KIP126.Main
import all KIP126.Main.BoundaryFormula
import all KIP126.Main.ChoiceIndependence
import all KIP126.Main.Internal.Choice.Completion
import all KIP126.Main.ClassicalReduction
import all KIP126.Main.Conditions
import all KIP126.Main.DifferentialReduction
import all KIP126.Main.H6SquarePermanent
import all KIP126.Main.Internal.AlphaOne.Classical
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.Internal.AlphaOne.Corrections
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.AlphaOne.ErrorFiltration
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.Internal.AlphaOne.Filtration
import all KIP126.Main.Internal.AlphaOne.FiniteFrames
import all KIP126.Main.Internal.AlphaOne.FiniteWindow
import all KIP126.Main.Internal.AlphaOne.LastDifferential
import all KIP126.Main.Internal.AlphaOne.Layers
import all KIP126.Main.Internal.AlphaOne.PageConsequences
import all KIP126.Main.Internal.AlphaOne.PageVanishing
import all KIP126.Main.Internal.AlphaOne.Quotients
import all KIP126.Main.Internal.AlphaOne.Staircase
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.Choice.FinitePages
import all KIP126.Main.Internal.Choice.Gap
import all KIP126.Main.Internal.Choice.Invariance
import all KIP126.Main.Internal.Choice.LambdaInjectivity
import all KIP126.Main.Internal.Choice.OrderTwo
import all KIP126.Main.Internal.Choice.PageFrames
import all KIP126.Main.Internal.CofiberRigidity
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.FiniteReflection
import all KIP126.Main.Internal.High125.Detector
import all KIP126.Main.Internal.High125.Differential
import all KIP126.Main.Internal.High125.Filtration
import all KIP126.Main.Internal.High125.Finite
import all KIP126.Main.Internal.High125.Injectivity
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.High125.Source
import all KIP126.Main.Internal.High125.Tail
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.LowEta
import all KIP126.Main.Internal.NuFifth.Frame
import all KIP126.Main.Internal.NuFifth.Lift
import all KIP126.Main.Internal.NuNinth.Assembly
import all KIP126.Main.Internal.NuNinth.Fourth
import all KIP126.Main.Internal.NuNinth.Frames
import all KIP126.Main.Internal.NuNinth.Incoming
import all KIP126.Main.Internal.NuNinth.Lift
import all KIP126.Main.Internal.NuNinth.Shift
import all KIP126.Main.Internal.NuNinth.Unit
import all KIP126.Main.Internal.NuThree.Actual
import all KIP126.Main.Internal.NuThree.ActualOperations
import all KIP126.Main.Internal.NuThree.Assembly
import all KIP126.Main.Internal.NuThree.ClassicalZero
import all KIP126.Main.Internal.NuThree.Finite
import all KIP126.Main.Internal.NuThree.Mahowald
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.NuThree.Suspension
import all KIP126.Main.Internal.NuThree.ZeroExtensions
import all KIP126.Main.Internal.NuThree.ZeroLabels
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.Assembly
import all KIP126.Main.Internal.Selected.Classical
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.Selected.Exhaustion
import all KIP126.Main.Internal.Selected.FinitePages
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.NuErrorData
import all KIP126.Main.Internal.Selected.ProductDetection
import all KIP126.Main.Internal.Selected.ProductZero
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.TargetFrame
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Theta.Detection
import all KIP126.Main.Internal.Theta.NoCrossing
import all KIP126.Main.Internal.Theta.OrderTwo
import all KIP126.Main.Internal.Theta.Products
import all KIP126.Main.Internal.Theta.RealizationKernel
import all KIP126.Main.Internal.Theta.Shuffle
import all KIP126.Main.Internal.Theta.TodaAlgebra
import all KIP126.Main.Internal.Theta.TodaCofiber
import all KIP126.Main.Internal.Theta.TodaExistence
import all KIP126.Main.Internal.Theta.TodaIndeterminacy
import all KIP126.Main.Internal.Theta.ZeroDegree
import all KIP126.Main.DifferentialCriterion
import all KIP126.Main.RepresentativeResults
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.AnyYError
import all KIP126.Main.SectionSeven.AnyYFinite
import all KIP126.Main.SectionSeven.AnyYPeeling
import all KIP126.Main.SectionSeven.AnyYShuffle
import all KIP126.Main.SectionSeven.AnyYSplit
import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.CofiberRigidity
import all KIP126.Main.SectionSeven.Final
import all KIP126.Main.SectionSeven.Indeterminacy
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.SectionSeven.NuFifthAction
import all KIP126.Main.SectionSeven.NuTarget
import all KIP126.Main.SectionSeven.NuTargetCommute
import all KIP126.Main.SectionSeven.NuTargetCosets
import all KIP126.Main.SectionSeven.NuTargetDetection
import all KIP126.Main.SectionSeven.NuTargetE2Calculus
import all KIP126.Main.SectionSeven.NuTargetFinite
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
import all KIP126.Main.SectionSeven.NuTargetFrame
import all KIP126.Main.SectionSeven.NuTargetFull
import all KIP126.Main.SectionSeven.NuTargetH0Products
import all KIP126.Main.SectionSeven.NuTargetLambda
import all KIP126.Main.SectionSeven.NuTargetLinear
import all KIP126.Main.SectionSeven.NuTargetPeeling
import all KIP126.Main.SectionSeven.NuTargetProducts
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.SectionSeven.NuTargetYLambda
import all KIP126.Main.SectionSeven.NuTargetYRelation
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.ThetaEta
import all KIP126.Main.SectionSeven.ThetaToda
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.SectionSeven.WeakInitialLambda
import all KIP126.Main.SectionSeven.WeakInitialNonzero
import all KIP126.Main.SectionSeven.WeakRepresentative
import all KIP126.Main.SectionSeven.WeakStrip
import all KIP126.Main.SectionSeven.WeakStripFinite
import all KIP126.Main.SectionSeven.WeakStripTorsion
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.SectionSeven.WeakYFinite
import all KIP126.Main.SquareClassification
import all KIP126.Main.TableOne


public meta import Checks.Registry
import Lean

/-! Trust audit for article-owned proof and construction responsibilities. Only the exact individually
registered proof/construction holes are permitted; project axioms and synthetic
(elaboration-error) holes are always rejected. SpectralSequence stays sorry-free. -/
-- Former public-consumer examples remain checked inside Main after encapsulation.
namespace KIP126.Main.InternalAudit
open KIP126.Main KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta bxTheta5)

example : ∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u :=
  u_choice_exists

example (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    ∃ y : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      lambdaMultiply 3 (sphereProduct eta u) = lambdaMultiply 6 y :=
  lambda_three_eta_u_eq_lambda_six u hu

example (u v : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hu : UChoice u) (hv : UChoice v) :
    FiltrationAtLeast model.syntheticTower 14
      (lambdaMultiply 3 (sphereProduct eta u) -
        lambdaMultiply 3 (sphereProduct eta v)) :=
  lambda_three_eta_u_difference_filtration_fourteen u v hu hv

example (hc3 : Stem126D6Vanishes) (h : ∀ u, UChoice u → EtaExtensionDetectionAt u) : False := table1 hc3 h

-- Recover the former three-possibility shape with actual representatives.
example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (_htheta : ThetaChoice theta) :
    (∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u ∧
      sphereProduct theta theta = lambdaMultiply 6 u) ∨
    (∃ c : BiHom 124 137 (S_0_0 : SyntheticSpectrum),
      sphereProduct theta theta = lambdaMultiply 9 c) ∨
    (∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum),
      sphereProduct theta theta = lambdaMultiply 10 a) := by
  rcases theta_square_three_possibilities theta with h6 | h9 | h10
  · exact Or.inl h6
  · obtain ⟨c, _, hc⟩ := h9
    exact Or.inr (Or.inl ⟨c, hc⟩)
  · exact Or.inr (Or.inr h10)

example : KIP126.Literature.deltaH6Square model =
    KIP126.Literature.Standard.lambdaEtaThetaSquare bxTheta5 :=
  delta_h6_square_bx

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.deltaH6Square model =
      KIP126.Literature.Standard.lambdaEtaThetaSquare theta :=
  delta_h6_square_eq_lambda_eta_theta_square theta htheta

example : Stem126D6Vanishes ↔
    KIP126.Core.SpectralSequence.SurvivesTo model.classical.sphere 12 (14,139)
      KIP126.Computation.Standard.T := d6_vanishes_iff_target_survives_twelve

end KIP126.Main.InternalAudit


open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  let expected : Array Json ← entries.filterM fun (row : Json) => do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    pure ((`KIP126.Main).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Main).isPrefixOf mod do continue
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
  logInfo m!"Main trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"

-- Public results and internal replacements retain their reviewed local
-- proof dependencies. Upstream obligations remain owned by upstream modules.
run_cmd do
  let env ← getEnv
  let checks : Array (Name × Array Name) := #[
    (`KIP126.Main.u_choice_exists, #[]),
    (`KIP126.Main.lambda_three_eta_u_filtration_fourteen, #[]),
    (`KIP126.Main.lambda_three_eta_u_eq_lambda_six, #[]),
    (`KIP126.Main.lambda_three_eta_u_difference_filtration_fourteen, #[]),
    (`KIP126.Main.table1, #[]),
    (`KIP126.Main.theta_square_detection_cases, #[]),
    (`KIP126.Main.theta_square_three_possibilities, #[]),
    (`KIP126.Main.delta_h6_square_bx, #[]),
    (`KIP126.Main.delta_h6_square_eq_lambda_eta_theta_square, #[]),
    (`KIP126.Main.normalized_bx_finite, #[]),
    (`KIP126.Main.h6_square_basis, #[]),
    (`KIP126.Main.h6_square_reaches_seven, #[]),
    (`KIP126.Main.h6_square_survives_three, #[]),
    (`KIP126.Main.lambda_eta_theta_square_mod_lambda_zero, #[]),
    (`KIP126.Main.any_choice_criterion, #[]),
    (`KIP126.Main.lambda_eta_theta_square_independent, #[]),
    (`KIP126.Main.eta_extension_detection_choice_equivalence, #[])]
  for (root, expected) in checks do
    let roots := env.constants.toList.filter fun (name, _) =>
      ((privateToUserName? name).getD name) == root
    unless roots.length == 1 do
      throwError "Missing unique Main declaration: {root}"
    let mut todo := #[roots.head!.1]
    let mut visited : NameSet := {}
    let mut actual : Array Name := #[]
    while let some name := todo.back? do
      todo := todo.pop
      if visited.contains name then continue
      visited := visited.insert name
      let some info := env.find? name
        | throwError "Missing proof dependency while auditing {root}: {name}"
      let some idx := env.getModuleIdxFor? name | continue
      unless (`KIP126.Main).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
      let body := info.value? (allowOpaque := true)
      if info.type.hasSorry || body.any (·.hasSorry) then
        actual := actual.push name
      todo := todo ++ info.type.getUsedConstants
      if let some value := body then todo := todo ++ value.getUsedConstants
    unless (actual.map Name.toString).qsort (· < ·) ==
        (expected.map Name.toString).qsort (· < ·) do
      throwError "Main proof dependencies changed for {root}: {actual}; expected {expected}"
  logInfo m!"Main legacy-result audit: {checks.size} public/internal results have the exact reviewed local proof dependencies"

-- The updated Nu9 proof uses only the finite Y incoming window.
run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filter fun (name, _) =>
    ((privateToUserName? name).getD name) ==
      `KIP126.Main.Internal.NuNinth.nu_ninth_of_fifth_complete
  unless roots.length == 1 do
    throwError "Missing unique Nu9 finite-window proof"
  let mut todo := roots.toArray.map (·.1)
  let mut visited : NameSet := {}
  while let some name := todo.back? do
    todo := todo.pop
    if name == `KIP126.Computation.Standard.y_not_hit then
      throwError "Nu9 regained the unrestricted Y incoming assumption"
    if visited.contains name then continue
    visited := visited.insert name
    let some info := env.find? name | continue
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.Main).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    todo := todo ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  logInfo "Nu9 finite-window dependency audit: no unrestricted Y incoming assumption"


run_cmd do
  let env ← getEnv
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
    let candidates := env.constants.toList.filter fun (n, _) =>
      ((privateToUserName? n).getD n) == name
    unless candidates.length == 1 do
      throwError "Missing unique paper proof assembly: {name}"
    let info := candidates.head!.2
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Paper proof assembly was replaced by a direct placeholder: {name}"


-- Normal imports deliberately hide ProofTools proof bodies. Audit every Main
-- body here and freeze the exact hand-off to the same-module ProofTools audit;
-- that audit recursively checks these boundary declarations with full bodies.
-- The independent full-body dependency observer checks the composed graph.
run_cmd do
  let contract ← Lean.ofExcept <| Json.parse (include_str "../../metadata/main-api.json")
  let rows ← Lean.ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let roots ← rows.mapM fun row => do
    let name ← Lean.ofExcept <| row.getObjValAs? String "name"
    pure name.toName
  let ledger ← Lean.ofExcept <| Json.parse proofObligationLedger
  let route ← Lean.ofExcept <| ledger.getObjVal? "main_zero_layer_rewire_2026_10_16"
  let boundaryNames ← Lean.ofExcept <| route.getObjValAs? (Array String)
    "proofTools_boundary_declarations"
  let reviewedProofToolsBoundary := boundaryNames.map String.toName
  let reviewedRootNames ← Lean.ofExcept <| route.getObjValAs? (Array String)
    "public_main_roots"
  unless (roots.map Name.toString).qsort (· < ·) == reviewedRootNames.qsort (· < ·) do
    throwError "Reviewed Main roots differ from the frozen public interface"
  let forbidden := #[`KIP126.ProofTools.Standard.generalizedMahowald,
    `KIP126.ProofTools.Standard.generalizedLeibniz]
  let env ← getEnv
  let mut boundary : NameSet := {}
  let mut checkedMain : NameSet := {}
  for root in roots do
    unless env.contains root do
      throwError "Missing locked Main public root: {root}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then
        throwError "Main public root {root} regained an unfinished MH2/GL dependency: {name}"
      let some info := env.find? name
        | throwError "Missing dependency while auditing Main public root {root}: {name}"
      let some idx := env.getModuleIdxFor? name
        | if (`KIP126).isPrefixOf ((privateToUserName? name).getD name) then
            throwError "Missing project module provenance while auditing {root}: {name}"
          continue
      let mod := env.header.moduleNames[idx.toNat]!
      let isMain := (`KIP126.Main).isPrefixOf mod
      let isProofTools := (`KIP126.ProofTools).isPrefixOf mod
      unless isMain || isProofTools do continue
      let body := info.value? (allowOpaque := true)
      if info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry) then
        throwError "Synthetic sorry reachable from Main public root {root}: {name}"
      if info.type.hasSorry || body.any (·.hasSorry) then
        throwError "Main/ProofTools placeholder reachable from Main public root {root}: {name}"
      if isProofTools then
        -- An imported theorem can be represented as an axiom with no body.
        -- Never interpret that absence as a completed cross-module audit.
        unless reviewedProofToolsBoundary.contains name do
          throwError "Unreviewed ProofTools audit boundary from Main public root {root}: {name}"
        boundary := boundary.insert name
        continue
      if info.isAxiom then
        throwError "Main declaration has no auditable proof body: {name} (root {root})"
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless body.isSome do
          throwError "Missing Main definition/proof body while auditing {root}: {name}"
      | _ => pure ()
      checkedMain := checkedMain.insert name
      pending := pending ++ info.type.getUsedConstants
      if let some value := body then pending := pending ++ value.getUsedConstants
  -- Reject stale boundary entries as well as newly introduced dependencies.
  unless boundary.toArray.qsort Name.quickLt == reviewedProofToolsBoundary.qsort Name.quickLt do
    throwError "Main/ProofTools reviewed audit boundary changed: {boundary.toArray}"
  logInfo m!"Main public-root regression audit: {roots.size} roots, {checkedMain.size} Main declarations; no local placeholder or old MH2/GL; {boundary.size} exact ProofTools boundaries delegated to its full-body internal audit"
