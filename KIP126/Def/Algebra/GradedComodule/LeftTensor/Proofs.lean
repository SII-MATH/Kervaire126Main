module

public import KIP126.Def.Algebra.GradedComodule.LeftTensor.Data

@[expose] public section

/-! Properties of the prescribed left-tensored coaction. -/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem leftTensorCoaction_counit (C : Comon V) (X : V) (A : RightComodule C) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).ε.app (X ⊗ A.A) =
      𝟙 (X ⊗ A.A) := by
  change (X ◁ A.a ≫ (α_ X A.A C.X).inv) ≫
    ((X ⊗ A.A) ◁ ComonObj.counit ≫ (ρ_ (X ⊗ A.A)).hom) = _
  erw [Category.assoc, ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_rightUnitor, ← whiskerLeft_comp, ← whiskerLeft_comp]
  have h := A.counit
  change A.a ≫ (A.A ◁ ComonObj.counit ≫ (ρ_ A.A).hom) = 𝟙 A.A at h
  erw [h, whiskerLeft_id]

theorem leftTensorCoaction_coassoc (C : Comon V) (X : V) (A : RightComodule C) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).δ.app (X ⊗ A.A) =
      leftTensorCoaction C X A ≫
        (rightTensorComonad C).map (leftTensorCoaction C X A) := by
  change (X ◁ A.a ≫ (α_ X A.A C.X).inv) ≫
    ((X ⊗ A.A) ◁ ComonObj.comul ≫ (α_ (X ⊗ A.A) C.X C.X).inv) =
    (X ◁ A.a ≫ (α_ X A.A C.X).inv) ≫
      (X ◁ A.a ≫ (α_ X A.A C.X).inv) ▷ C.X
  have h := A.coassoc
  change A.a ≫ (A.A ◁ ComonObj.comul ≫ (α_ A.A C.X C.X).inv) =
    A.a ≫ A.a ▷ C.X at h
  have h' : A.a ≫ A.A ◁ ComonObj.comul =
      A.a ≫ A.a ▷ C.X ≫ (α_ A.A C.X C.X).hom := by
    calc
      _ = (A.a ≫ (A.A ◁ ComonObj.comul ≫ (α_ A.A C.X C.X).inv)) ≫
          (α_ A.A C.X C.X).hom := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := by
        erw [h, Category.assoc]
        rfl
  simp only [comp_whiskerRight, Category.assoc]
  erw [← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, h']
  simp only [whiskerLeft_comp, Category.assoc]
  erw [pentagon_hom_inv_inv_inv_inv]
  rfl

theorem leftTensorCoaction_map (C : Comon V) (X : V) {A B : RightComodule C}
    (f : A ⟶ B) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).map (X ◁ f.f) =
      (X ◁ f.f) ≫ leftTensorCoaction C X B := by
  change (X ◁ A.a ≫ (α_ X A.A C.X).inv) ≫ (X ◁ f.f) ▷ C.X =
    X ◁ f.f ≫ (X ◁ B.a ≫ (α_ X B.A C.X).inv)
  have h := f.h
  change A.a ≫ f.f ▷ C.X = f.f ≫ B.a at h
  erw [Category.assoc, ← associator_inv_naturality_middle,
    ← whiskerLeft_comp_assoc, h, whiskerLeft_comp_assoc]
  rfl

end KIP126.Algebra.GradedComodule
