module
import all KIP126.Main
import all KIP126.Main.BoundaryFormula
import all KIP126.Main.ChoiceIndependence
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

-- Public replacements for old Main axioms must retain their reviewed local
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
    (`KIP126.Main.delta_h6_square_eq_lambda_eta_theta_square,
      #[`KIP126.Main.lambda_eta_theta_square_independent])]
  for (root, expected) in checks do
    let mut todo := #[root]
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
  logInfo m!"Main legacy-result audit: {checks.size} public results have the exact reviewed local proof dependencies"

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
