module

public import KIP126.Def.ClassicalAdams.TowerLayer.Data

@[expose] public section

/-! Coefficient-homology resolution maps constructed directly from the Adams
unit and its chosen cofiber. No first-page coordinates are assumed. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The boundary of the unit fiber triangle, with the sign dictated by the
positive `fiberι` convention. Defined before any page differential comparison. -/
def adamsResolutionConnecting (s : ℕ) :
    H ⊗ adamsTower unit X s ⟶ (adamsTower unit X (s + 1))⟦(1 : ℤ)⟧ :=
  -(adamsFiberTriangle (adamsUnit unit (adamsTower unit X s))).mor₃

/-- The unit fiber triangle with the positive tower inclusion convention. -/
def adamsResolutionTriangle (s : ℕ) : Triangle C :=
  Triangle.mk (adamsTowerStep unit X s)
    (adamsUnit unit (adamsTower unit X s)) (adamsResolutionConnecting unit X s)

/-- The homotopy connecting map from coefficient homology to the next tower
term. This uses the unit's cofiber triangle, not an independently supplied map. -/
def adamsResolutionBoundary (s : ℕ) (n : ℤ) :
    HomotopyGroup n (H ⊗ adamsTower unit X s) →+
      HomotopyGroup (n - 1) (adamsTower unit X (s + 1)) where
  toFun z := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map (z ≫ adamsResolutionConnecting unit X s) ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (adamsTower unit X (s + 1))
  map_zero' := by simp
  map_add' a b := by simp [Preadditive.add_comp, Preadditive.comp_add]

/-- The resolution differential: connecting map followed by the next Adams
unit. The degree cast expresses `t - s - 1 = t - (s + 1)`. -/
def adamsResolutionDifferential (s : ℕ) (t : ℤ) :
    HomotopyGroup (t - s) (H ⊗ adamsTower unit X s) →ₗ[ℤ]
      HomotopyGroup (t - (s + 1 : ℕ)) (H ⊗ adamsTower unit X (s + 1)) :=
  (inducedMap (adamsUnit unit (adamsTower unit X (s + 1))) (t - (s + 1 : ℕ))).toIntLinearMap.comp
    ((LinearEquiv.cast (R := ℤ)
      (M := fun n => HomotopyGroup n (adamsTower unit X (s + 1)))
      (by omega : t - s - 1 = t - (s + 1 : ℕ))).toLinearMap.comp
      (adamsResolutionBoundary unit X s (t - s)).toIntLinearMap)

end

end KIP126.Classical.Adams
