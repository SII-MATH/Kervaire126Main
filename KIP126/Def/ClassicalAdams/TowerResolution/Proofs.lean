module

public import KIP126.Def.ClassicalAdams.TowerResolution.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.ClassicalAdams.TowerDifferential.Proofs
import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

/-! Comparison of the actual first differential with the resolution formula. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Correct the two signs of inverse rotation by the negative identity on the
fiber. The result uses exactly the positive inclusion defining the tower. -/
theorem adamsResolutionTriangle_distinguished (s : ℕ) :
    adamsResolutionTriangle unit X s ∈ distTriang C := by
  apply isomorphic_distinguished _
    (adamsFiberTriangle_distinguished (adamsUnit unit (adamsTower unit X s)))
  exact Triangle.isoMk _ _ (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by simp [adamsResolutionTriangle, adamsFiberTriangle_mor₁, adamsTowerStep])
    (by simp [adamsResolutionTriangle, adamsFiberTriangle, Triangle.invRotate])
    (by simp [adamsResolutionTriangle, adamsResolutionConnecting])

end

end KIP126.Classical.Adams
