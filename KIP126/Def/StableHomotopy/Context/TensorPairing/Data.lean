module

public import KIP126.Def.StableHomotopy.Context.Data
public import Mathlib.CategoryTheory.Monoidal.Preadditive

@[expose] public section

namespace KIP126.StableHomotopy

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The specified sphere tensor comparison from the given right-tensor shift
comparison. No symmetry or graded-sign coherence is asserted here. -/
def sphereTensorIsoFromRightShift (a b : ℤ)
    [(tensorRight (Sphere b : C)).CommShift ℤ] :
    (Sphere a : C) ⊗ Sphere b ≅ Sphere (a + b) :=
  (Functor.commShiftIso (tensorRight (Sphere b : C)) a).app (𝟙_ C) ≪≫
    (shiftFunctor C a).mapIso (λ_ (Sphere b)) ≪≫
    ((shiftFunctorAdd' C b a (a + b) (by omega)).app (𝟙_ C)).symm

variable [MonoidalPreadditive C]

/-- Tensor two represented morphisms and then compose with an actual pairing.
Additivity of tensor makes this integer-bilinear. -/
def tensorHomPairing {A B W X Y Z : C} (w : W ⟶ A ⊗ B) (f : X ⊗ Y ⟶ Z) :
    (A ⟶ X) →ₗ[ℤ] (B ⟶ Y) →ₗ[ℤ] (W ⟶ Z) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => AddMonoidHom.toIntLinearMap
        { toFun := fun y => w ≫ (x ⊗ₘ y) ≫ f
          map_zero' := by simp
          map_add' := by
            intro y z
            simp only [MonoidalPreadditive.tensor_add, Preadditive.add_comp,
              Preadditive.comp_add] }
      map_zero' := by ext y; simp
      map_add' := by
        intro x y
        ext z
        change w ≫ ((x + y) ⊗ₘ z) ≫ f =
          (w ≫ (x ⊗ₘ z) ≫ f) + (w ≫ (y ⊗ₘ z) ≫ f)
        simp only [MonoidalPreadditive.add_tensor,
          Preadditive.add_comp, Preadditive.comp_add] }

/-- Pair actual homotopy classes using the specified sphere comparison.
The equality allows the target degree to retain its existing indexing. -/
def homotopyTensorPairing (a b n : ℤ) (h : n = a + b)
    [(tensorRight (Sphere b : C)).CommShift ℤ] {X Y Z : C}
    (f : X ⊗ Y ⟶ Z) :
    HomotopyGroup a X →ₗ[ℤ] HomotopyGroup b Y →ₗ[ℤ] HomotopyGroup n Z :=
  tensorHomPairing
    (eqToHom (congrArg (Sphere (C := C)) h) ≫
      (sphereTensorIsoFromRightShift (C := C) a b).inv) f

end
end KIP126.StableHomotopy
