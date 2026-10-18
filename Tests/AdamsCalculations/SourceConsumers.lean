module

import KIP126.AdamsCalculations

/-! Cofiber finite-page consumers use the actual Adams calculation entry. -/
namespace Tests.AdamsCalculations.SourceConsumers
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

theorem cofiberFiniteSurvival :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) ∧
      NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) :=
  ⟨cofiber_target_to_e6, cofiber_target_not_hit_through5⟩

#check_failure KIP126.Computation.ComputationResults
#check_failure KIP126.Computation.Bindings

end Tests.AdamsCalculations.SourceConsumers
