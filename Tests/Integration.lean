module

import KIP126.Computation
import Lean

open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard

-- The goal uses the fixed sphere and its actual multiplication. No upstream
-- result package, construction witness, or extra theorem hypothesis is needed.
example : Prop := NonzeroSurvival model.classical.sphere (2,128)
  model.standardClasses.standardH6Square

example : KIP126.Computation.Standard.atom .g = KIP126.Literature.Standard.g :=
  KIP126.Computation.Standard.g_agrees

example : HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    KIP126.Computation.Standard.h6
    (KIP126.Computation.Standard.product KIP126.Computation.Standard.h0
      KIP126.Computation.Standard.h5Square) :=
  KIP126.Computation.Standard.d2_h6

#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results
#check_failure KIP126.Main.Axiom.challenge2

-- New source facts and finite-page screening are independently consumable
-- before Main, including the unbounded HHR range.
example : KIP126.AdamsCalculations.TwoLineD2Candidate 100 100 := by
  unfold KIP126.AdamsCalculations.TwoLineD2Candidate
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

example : KIP126.AdamsCalculations.TwoLineD2Candidate 0 4 := by
  unfold KIP126.AdamsCalculations.TwoLineD2Candidate
  omega

example : ∃ y : model.classical.sphere.Page 2 (5,19),
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) y :=
  KIP126.Literature.Standard.iwx_h0_h4_d3

example (j : ℕ) (hj : 7 ≤ j) :
    ¬ NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) :=
  KIP126.Literature.Standard.hhr_high_squares_not_permanent j hj

example (i j : ℕ) (hij : i ≤ j)
    (hne : KIP126.Literature.Standard.hiProduct i j ≠ 0)
    (hr : ReachesPage model.classical.sphere 3
      (KIP126.Classical.Adams.hiDegree i + KIP126.Classical.Adams.hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j)) :
    KIP126.AdamsCalculations.TwoLineD2Candidate i j :=
  KIP126.AdamsCalculations.two_line_d2_candidates i j hij hne hr

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod then
      throwError "Integration consumer imported a retired delivery or Main: {mod}"
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
        throwError "Consumer supplied an unfinished proof: {name}"
