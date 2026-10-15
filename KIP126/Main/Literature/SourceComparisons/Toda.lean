module

public import KIP126.Main.ExternalHypotheses.Data
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

-- Keep the original instance parameters of this public theorem.
set_option linter.unusedSectionVars false in
/-- Transport the actual secondary-operation calculation, retaining its
star/product identification. BHS ring facts alone are not sufficient. -/
theorem todaApplication_of_secondary (η : BiHom 1 2 (S_0_0 : Syn))
    (S : SyntheticH0Class (Syn := Syn)) (B : TodaSecondaryComparison η S) :
    TodaComparisonRelations η S := by
  refine ⟨B.low_bracket, ?_⟩
  intro θ hθ
  rw [← B.star_product θ]
  exact B.symmetric θ hθ

/-- The secondary Toda relations follow from the specified source facts
and the comparison of secondary operations on the same sphere. -/
theorem toda_of_source (η : BiHom 1 2 (S_0_0 : Syn)) (S : SyntheticH0Class (Syn := Syn))
    (A : TodaSourceResults D η S) (B : TodaSecondaryComparison η S) :
    Nonempty (TodaRelations D η) := by
  exact ⟨todaRelationsOfSource D η S A (todaApplication_of_secondary η S B)⟩

end
end KIP126.Main.Literature.SourceComparisons
