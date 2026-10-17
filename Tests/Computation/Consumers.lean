module

import KIP126.Computation
import KIP126.Computation.Table.Internal.SourceExpression

/-! Consumers use the fixed objects and callable source theorems. Only actual
mathematical variables and range hypotheses are parameters. -/
namespace Tests.Computation
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

/-- No model, computation certificate or result package is an input. -/
theorem factSevenSix :
    SurvivesTo model.classical.sphere 6 (8,134) W ∧
      IsPermanentCycle model.classical.sphere (14,139) T ∧
      NonzeroSurvival model.classical.sphere (10,134) U :=
  ⟨w_to_e6, t_permanent_cycle, u_permanent⟩

theorem allIncomingPages {r s t : ℤ} (hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : model.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential model.classical.sphere r (s,t) (14,139) x T :=
  no_other_incoming hr h6 h12 x

theorem tableNine (r : ℤ) (hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential model.classical.sphere r (6,132) (14,139)
      (atom .x_126_6) T := table9 r hr

theorem tableThree :
    SurvivesTo model.classical.sphere 12 (9,132) V ∧
    NeverHit model.classical.sphere (9,132) V ∧
    HasNonzeroDifferential model.classical.sphere 2 (8,133) (10,134)
      (atom .x_125_8) d2Target := table3

theorem tableSeven :
    SurvivesTo model.classical.sphere 5 (11,136) Y ∧
      NeverHit model.classical.sphere (11,136) Y := table7

theorem tableTwo :
    (SurvivesTo model.classical.sphere 6 (8,130) X ∧
      NeverHit model.classical.sphere (8,130) X) ∧
    (IsPermanentCycle model.classical.sphere (11,133) P ∧
      IsPermanentCycle model.classical.sphere (12,134) Q) := table2

/-- Full coordinate completeness retains the source archive and bound. -/
theorem archivedBasis (s t : ℕ) (ht : t ≤ 261) (i : Fin (archive.basisCount s t)) :
    (comparison s t ht).symm ((coordinates s t ht).symm (Finsupp.single i 1)) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator :=
  comparison_symm_coordinates_basis s t ht i

theorem productComparison (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t') :
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      model.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y) :=
  comparison_product s t s' t' ht x y

theorem squareIdentification :
    comparison 2 128 (by decide)
      (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)) =
      model.standardClasses.standardH6Square := h6_square

theorem cofiberFiniteSurvival :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) ∧
      NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) :=
  ⟨cofiber_target_to_e6, cofiber_target_not_hit_through5⟩

/-- Finite survival and permanent-cycle statements retain different strengths. -/
example : True := by
  fail_if_success have _ : NonzeroSurvival model.classical.sphere (8,134) W := w_to_e6
  fail_if_success have _ : NonzeroSurvival model.classical.sphere (14,139) T := t_permanent_cycle
  trivial

/-- Bounded coordinates cannot be applied outside their certified range. -/
example : True := by
  fail_if_success have _ := comparison 2 262 (by decide)
  trivial

theorem literatureOneLine :
    HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65) h6 (product h0 h5Square) := d2_h6

theorem detectorSourceComparison :
    HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
      (detectorComparison 16 112 (by decide) detectorV2Sixteen)
      (detectorComparison 19 114 (by decide) detectorBetaGFour) := detector_d3

theorem sharedLiteratureLabel : atom .g = KIP126.Literature.Standard.g := g_agrees

#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Computation.ComputationResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results
#check_failure KIP126.Computation.Bindings
end Tests.Computation

-- Direct ordinary imports must keep the new comparison helper private.
#check_failure KIP126.Computation.Table.sourceValue
#check_failure KIP126.Computation.Table.value_comparison
