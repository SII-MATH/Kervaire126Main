module

public import KIP126.Def.ClassicalAdams.TowerRepresentatives.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The representative equivalence carries exactly the actual tower boundaries,
not just an unspecified submodule of equal dimension. -/
theorem adamsFiniteCycleEquiv_boundaries (s t : ℤ) (n : ℕ) :
    ((adamsFiniteBoundarySubmodule unit X s t n).comap
      (adamsFiniteCycleSubmodule unit X s t n).subtype).map
        (adamsFiniteCycleEquiv unit X s t n).toLinearMap =
      adamsCycleBoundaries unit X (n + 2) (by omega) s t := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(adamsFiniteCycleEquiv unit X s t n).symm x, hx,
      (adamsFiniteCycleEquiv unit X s t n).apply_symm_apply x⟩

end
end KIP126.Classical.Adams
