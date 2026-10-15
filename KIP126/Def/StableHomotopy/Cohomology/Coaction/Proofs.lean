module

public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Basic.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- Naturality of the actual unit used in every stage of the Adams tower. -/
theorem mod2AdamsUnit_naturality {X Y : C} (f : X ⟶ Y) :
    adamsUnit H.unit X ≫ H.HF2 ◁ f = f ≫ adamsUnit H.unit Y := by
  simp only [adamsUnit, Category.assoc]
  rw [← whisker_exchange, ← Category.assoc, ← leftUnitor_inv_naturality,
    Category.assoc]

/-- Naturality before passing to coefficient homology or coordinates. -/
theorem mod2Coaction_naturality {X Y : C} (f : X ⟶ Y) :
    mod2Coaction H X ≫ H.HF2 ◁ (H.HF2 ◁ f) =
      H.HF2 ◁ f ≫ mod2Coaction H Y := by
  simp only [mod2Coaction, ← whiskerLeft_comp, mod2AdamsUnit_naturality]

/-- Multiplication on the first two factors is a counit for unit insertion. -/
theorem mod2Coaction_counit (R : Mod2RingStructure H) (X : C) :
    mod2Coaction H X ≫ mod2FreeAction H R X = 𝟙 _ :=
  mod2FreeAction_unit H R X

/-- On homology, insertion is a natural operation. -/
theorem mod2CoactionMap_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n X) :
    Mod2Homology.pushforward H (H.HF2 ◁ f) n (mod2CoactionMap H X n x) =
      mod2CoactionMap H Y n (Mod2Homology.pushforward H f n x) := by
  change (x ≫ _) ≫ _ = (x ≫ _) ≫ _
  rw [Category.assoc, mod2Coaction_naturality, Category.assoc]

end KIP126.StableHomotopy.Cohomology
