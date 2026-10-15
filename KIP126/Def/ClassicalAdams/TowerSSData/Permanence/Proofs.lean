module

public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Predicates

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Zero in a tower quotient means membership in its actual boundary submodule. -/
theorem adamsPage_mk_eq_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : adamsCycles unit X r hr s t) :
    (adamsCycleBoundaries unit X r hr s t).mkQ z = 0 ↔
      z.val ∈ adamsBoundaries unit X r hr s t :=
  Submodule.Quotient.mk_eq_zero (adamsCycleBoundaries unit X r hr s t)

end
end KIP126.Classical.Adams
