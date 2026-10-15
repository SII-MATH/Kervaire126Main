module

public import KIP126.Main.ExternalHypotheses.Data

@[expose] public section

/-! The tmf detection condition used in the proof of Proposition 7.8. -/
namespace KIP126.Main.SectionSeven.DifferentialCriterion

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.AdamsSynthetic

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- Injectivity of the tmf detector on an Adams filtration subgroup.
Proposition 7.8 uses `(m,w,s) = (125,130,15)`; Main proves this injectivity
from the literature and computation hypotheses. -/
def DetectorInjectiveAt (m w s : ℤ) : Prop :=
  ∀ α : BiHom m w (S_0_0 : Syn),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s α →
    α ≫ KIP126.Literature.AdamsSynthetic.detectorMap D = 0 → α = 0

end KIP126.Main.SectionSeven.DifferentialCriterion
