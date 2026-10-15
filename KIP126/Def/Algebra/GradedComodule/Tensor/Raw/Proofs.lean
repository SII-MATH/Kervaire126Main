module

public import KIP126.Def.Algebra.GradedComodule.Tensor.Raw.Data

@[expose] public section

/-! Naturality and laws of the explicitly given right-tensor maps. These
generic statements are separated from the data; their proofs are not part
of the current statement-definition milestone. -/

namespace KIP126.Algebra.GradedComodule.RightTensor

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem counit_naturality (C : Comon V) {X Y : V} (f : X ⟶ Y) :
    (tensorRight C.X).map f ≫ counitApp C Y = counitApp C X ≫ f := by
  dsimp [counitApp, tensorRight, curriedTensor, Functor.flip]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [Category.assoc]

theorem comul_naturality (C : Comon V) {X Y : V} (f : X ⟶ Y) :
    (tensorRight C.X).map f ≫ comulApp C Y =
      comulApp C X ≫ (tensorRight C.X).map ((tensorRight C.X).map f) := by
  dsimp [comulApp, tensorRight, curriedTensor, Functor.flip]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left]
  simp only [Category.assoc]

theorem coassoc (C : Comon V) (X : V) :
    comulApp C X ≫ (tensorRight C.X).map (comulApp C X) =
      comulApp C X ≫ comulApp C (X ⊗ C.X) := by
  dsimp [comulApp, tensorRight, curriedTensor, Functor.flip]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
    ComonObj.comul_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [pentagon_hom_inv_inv_inv_inv]

theorem left_counit (C : Comon V) (X : V) :
    comulApp C X ≫ counitApp C (X ⊗ C.X) = 𝟙 (X ⊗ C.X) := by
  dsimp only [comulApp, counitApp]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ComonObj.comul_counit]
  rw [← rightUnitor_tensor_inv_assoc]
  simp

theorem right_counit (C : Comon V) (X : V) :
    comulApp C X ≫ (tensorRight C.X).map (counitApp C X) = 𝟙 (X ⊗ C.X) := by
  dsimp [comulApp, counitApp, tensorRight, curriedTensor, Functor.flip]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, ComonObj.counit_comul]
  simp

theorem trivial_counit {C : Comon V} (η : Coaugmentation C) (X : V) :
    trivialCoaction η X ≫ counitApp C X = 𝟙 X := by
  dsimp only [trivialCoaction, counitApp]
  simp only [Category.assoc, ← whiskerLeft_comp_assoc]
  erw [η.isComonHom_hom.hom_counit]
  simp [Comon.trivial]

theorem trivial_coassoc {C : Comon V} (η : Coaugmentation C) (X : V) :
    trivialCoaction η X ≫ comulApp C X =
      trivialCoaction η X ≫ (tensorRight C.X).map (trivialCoaction η X) := by
  dsimp [trivialCoaction, comulApp, tensorRight, curriedTensor, Functor.flip]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whiskerLeft_comp_assoc]
  erw [η.isComonHom_hom.hom_comul]
  change (ρ_ X).inv ≫ X ◁ ((λ_ (𝟙_ V)).inv ≫ (η.hom ⊗ₘ η.hom)) ≫
    (α_ X C.X C.X).inv = _
  simp only [whiskerLeft_comp, tensorHom_def', Category.assoc]
  erw [associator_inv_naturality_middle,
    associator_inv_naturality_right_assoc, triangle_assoc_comp_left_inv_assoc,
    ← whisker_exchange_assoc]

theorem trivial_naturality {C : Comon V} (η : Coaugmentation C)
    {X Y : V} (f : X ⟶ Y) :
    trivialCoaction η X ≫ (tensorRight C.X).map f = f ≫ trivialCoaction η Y := by
  dsimp [trivialCoaction, tensorRight, curriedTensor, Functor.flip]
  rw [Category.assoc, whisker_exchange]
  rw [← Category.assoc, ← rightUnitor_inv_naturality]
  simp only [Category.assoc]

end KIP126.Algebra.GradedComodule.RightTensor
