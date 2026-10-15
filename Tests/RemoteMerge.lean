module

import KIP126
import Lean

/-! Ordinary-import consumers of the proofs ported from develop. The new
choice proofs must not acquire the existing Section 6 sorry dependencies. -/
open CategoryTheory KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Main.AdamsSynthetic
open KIP126.Kervaire.SyntheticTheta5

example (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData theta) :
    SurvivesTo sphereAdamsData 3 (2, 128) standardH6Square ↔
      VanishesModLambda 1 (lambdaEtaThetaSquare etaClass theta) :=
  (KIP126.Main.any_choice_criterion theta htheta).1 0

example (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData theta) :
    NonzeroSurvival sphereAdamsData (2, 128) standardH6Square ↔
      lambdaEtaThetaSquare etaClass theta = 0 :=
  (KIP126.Main.any_choice_criterion theta htheta).2

universe v

example {E E' : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (e : E ≅ E') (p : ℤ × ℤ) (x : E.Page 2 p) :
    NonzeroSurvival E' p (e.hom.pageMap 2 p x) ↔ NonzeroSurvival E p x :=
  nonzeroSurvival_iso_iff e p x

example : KIP126.Steenrod.Milnor.IsCycle KIP126.Steenrod.Milnor.unitCochain :=
  KIP126.Steenrod.Milnor.unitCochain_isCycle

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let accepted : List Name := [
    `propext, `Classical.choice, `Quot.sound,
    `KIP126.AdamsSynthetic.hf2AdamsContext_exists,
    `KIP126.StableHomotopy.Spectra.completionModel_exists,
    `KIP126.AdamsSynthetic.standardSyntheticContext,
    `KIP126.AdamsSynthetic.standardAdamsSyntheticComparisons,
    `KIP126.Def.standardSphereApplicability,
    `KIP126.Synthetic.SpectralSequence.CanonicalWeightShift.natural,
    `KIP126.Literature.adamsSyntheticResults,
    `KIP126.Computation.adamsComputations]
  let results := [
    ``KIP126.Main.any_choice_criterion,
    ``KIP126.Main.delta_h6_square_eq_lambda_eta_theta_square,
    ``KIP126.Main.theta5_square_nonzero_detection_choice_equivalence,
    ``KIP126.Main.eta_extension_detection_choice_equivalence,
    ``KIP126.Main.Stem126.BJMInduction.any_choice_criterion_of_theorems,
    ``KIP126.Main.ChoiceIndependence.square_and_eta_detection_choice_equivalence_proved,
    ``KIP126.SpectralSequence.nonzeroSurvival_map_of_injective,
    ``KIP126.SpectralSequence.nonzeroSurvival_iso_iff,
    ``KIP126.Steenrod.Milnor.unitCochain_isCycle,
    ``KIP126.Classical.Adams.MilnorCohomology.ofCocycle_surjective]
  for result in results do
    unless wasOriginallyTheorem env result do
      throwError "Ported result must be a theorem, not just a proposition definition: {result}"
    let axioms ← liftCoreM (collectAxioms result)
    for ax in axioms do
      unless accepted.contains ax do
        throwError "Ported result acquired an unapproved axiom or sorry: {result}: {ax}"
  logInfo m!"Remote merge: {results.length} theorem interfaces checked; r=0 consumer and no sorry dependencies"
