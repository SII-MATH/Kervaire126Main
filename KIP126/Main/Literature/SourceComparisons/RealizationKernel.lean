module

public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Main.Literature.AdamsSynthetic.Theorems

@[expose] public section

namespace KIP126.Main.Literature.SourceComparisons
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Transport the source localization-kernel theorem along the fixed
adjunction, λ action and realization comparisons for the specified objects. -/
theorem realizationKernel_of_source (S : SyntheticCompletionAdjunction Syn)
    (hS : RealizationKernelSourceResults D S) (B : RealizationKernelComparison D S) :
    RealizationKernel D := by
  intro X m w a
  rw [B.realization_zero X m w a, hS X m w (S.representatives _ m w a)]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (S.representatives _ m (w-k)).injective ?_⟩
    rw [map_zero, B.lambda X m w k a]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← B.lambda X m w k a, hk, map_zero]

end
end KIP126.Main.Literature.SourceComparisons
