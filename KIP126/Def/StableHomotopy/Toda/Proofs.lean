module

public import KIP126.Def.StableHomotopy.Toda.Predicates

@[expose] public section

/-!
# Basic properties of the shifted Toda relation

The proofs are adapted from the historical
`KIPBase/multiplicativeSS/TriangulatedTodaBracket.lean`; they do not use
historical declarations, project axioms, or proof placeholders.
-/

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- A Toda relation requires the two adjacent composites to vanish. -/
theorem composable {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) : f ≫ g = 0 ∧ g ≫ h = 0 := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  let T := Triangle.mk f i p
  have hfi : f ≫ i = 0 := by
    have h := comp_distTriang_mor_zero₁₂ T hT
    dsimp only [T, Triangle.mk] at h
    exact h
  have hip : i ≫ p = 0 := by
    have h := comp_distTriang_mor_zero₂₃ T hT
    dsimp only [T, Triangle.mk] at h
    exact h
  constructor
  · calc
      f ≫ g = (f ≫ i) ≫ gbar := by rw [← hg, Category.assoc]
      _ = 0 := by rw [hfi, zero_comp]
  · calc
      g ≫ h = i ≫ (gbar ≫ h) := by rw [← hg, Category.assoc]
      _ = (i ≫ p) ≫ x := by rw [← hx, Category.assoc]
      _ = 0 := by rw [hip, zero_comp]

/-- Every pair of vanishing adjacent composites admits a Toda representative. -/
theorem exists_relation {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) :
    ∃ x : X⟦(1 : ℤ)⟧ ⟶ W, Relation x f g h := by
  obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f i p
  obtain ⟨gbar, hgbar⟩ := T.yoneda_exact₂ hT g hfg
  dsimp only [T, Triangle.mk] at hgbar
  have hzero : i ≫ (gbar ≫ h) = 0 := by
    calc
      i ≫ (gbar ≫ h) = (i ≫ gbar) ≫ h := by simp only [Category.assoc]
      _ = g ≫ h := by rw [hgbar]
      _ = 0 := hgh
  obtain ⟨x, hx⟩ := T.yoneda_exact₃ hT (gbar ≫ h) hzero
  exact ⟨x, Q, i, p, hT, gbar, hgbar.symm, hx.symm⟩

/-- Adding a left-indeterminacy term preserves the Toda relation. -/
theorem indeterminacy_left {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (y : Y⟦(1 : ℤ)⟧ ⟶ W) :
    Relation (x + f⟦(1 : ℤ)⟧' ≫ y) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar, hg, ?_⟩
  have hpf : p ≫ f⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ (Triangle.mk f i p) hT
  calc
    p ≫ (x + f⟦(1 : ℤ)⟧' ≫ y) = p ≫ x + p ≫ (f⟦(1 : ℤ)⟧' ≫ y) := by
      simp only [Preadditive.comp_add]
    _ = p ≫ x + (p ≫ f⟦(1 : ℤ)⟧') ≫ y := by rw [Category.assoc]
    _ = p ≫ x := by rw [hpf, zero_comp, add_zero]
    _ = gbar ≫ h := hx

/-- Adding a right-indeterminacy term preserves the Toda relation. -/
theorem indeterminacy_right {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (z : X⟦(1 : ℤ)⟧ ⟶ Z) :
    Relation (x + z ≫ h) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar + p ≫ z, ?_, ?_⟩
  · have hip : i ≫ p = 0 :=
      comp_distTriang_mor_zero₂₃ (Triangle.mk f i p) hT
    calc
      i ≫ (gbar + p ≫ z) = i ≫ gbar + i ≫ (p ≫ z) := by
        simp only [Preadditive.comp_add]
      _ = g + (i ≫ p) ≫ z := by rw [hg, Category.assoc]
      _ = g := by rw [hip, zero_comp, add_zero]
  · calc
      p ≫ (x + z ≫ h) = p ≫ x + p ≫ (z ≫ h) := by
        simp only [Preadditive.comp_add]
      _ = gbar ≫ h + (p ≫ z) ≫ h := by rw [hx, Category.assoc]
      _ = (gbar + p ≫ z) ≫ h := by simp only [Preadditive.add_comp]

end KIP126.StableHomotopy.Toda
