module

import KIP126.AdamsCalculations

/-! Source-table and finite-page consumers use the actual Adams calculation entry. -/
namespace Tests.AdamsCalculations.SourceConsumers
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

theorem allIncomingPages {r s t : ℤ} (hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : model.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential model.classical.sphere r (s,t) (14,139) x T :=
  no_other_incoming hr h6 h12 x

theorem tableNine (r : ℤ) (hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential model.classical.sphere r (6,132) (14,139)
      (atom .x_126_6) T := table9 r hr

theorem tableSeven :
    SurvivesTo model.classical.sphere 5 (11,136) Y ∧
      NeverHit model.classical.sphere (11,136) Y := table7

theorem tableTwo :
    (SurvivesTo model.classical.sphere 6 (8,130) X ∧
      NeverHit model.classical.sphere (8,130) X) ∧
    (IsPermanentCycle model.classical.sphere (11,133) P ∧
      IsPermanentCycle model.classical.sphere (12,134) Q) := table2

theorem cofiberFiniteSurvival :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) ∧
      NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) :=
  ⟨cofiber_target_to_e6, cofiber_target_not_hit_through5⟩

theorem detectorSourceComparison :
    HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
      (detectorComparison 16 112 (by decide) detectorV2Sixteen)
      (detectorComparison 19 114 (by decide) detectorBetaGFour) := detector_d3

#check_failure KIP126.Computation.ComputationResults
#check_failure KIP126.Computation.Bindings

end Tests.AdamsCalculations.SourceConsumers
