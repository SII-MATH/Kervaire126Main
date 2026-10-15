module

public import KIP126.Main.Computation.Tmf.Model.Proofs

public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs

@[expose] public section

/-! BR21's source differential expressed in the fixed tmf coordinates.
The literature and computation hypotheses identify the same source classes;
Adams tower naturality transports the differential along that comparison. -/

namespace KIP126.Main.Computation

open KIP126.Classical.Adams KIP126.SpectralSequence

/-- Transport BR21's d₃(w₂²) = βg⁴ through the specified source comparison,
then use the proved identity βg⁴ = β⁵g in that same coordinate algebra.
This gives a differential equation, without asserting later-page nonvanishing. -/
theorem tmf_br21_d3 (input : KIP126.ExternalHypotheses) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
        KIP126.Def.standardTmfTarget.X)
      3 (16, 112) (19, 114)
      input.computation.interpretation.tmfCoordinates.v2Sixteen
      input.computation.interpretation.tmfCoordinates.betaFiveG := by
  have transported := adamsInternalE2Induced_hasDifferential
    standardFoundation.hf2.unit
    input.literature.sources.sourceComparisons.tmfComparison.detectorIso.inv
    input.literature.theorems.br21
  rw [← input.computation.interpretation.tmf_v2Sixteen,
    ← input.computation.interpretation.tmf_betaGFour,
    Tmf.E2Presentation.betaGFour_eq_betaFiveG] at transported
  exact transported

end KIP126.Main.Computation
