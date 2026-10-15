module

public import KIP126.Def.StableHomotopy.Toda.Proofs

@[expose] public section

/-! These proofs use the current cone-based `Relation` and Mathlib's
triangulated-category structure. They adapt the corresponding historical proofs
without importing `KIPBase` or its chosen models and global assumptions. -/

namespace KIP126.StableHomotopy.Toda

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Toda juggling with its shifted negative sign; this proof requires the octahedral axiom. -/
theorem juggling [IsTriangulated C]
    {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x f g h) (hhd : h ≫ d = 0) :
    ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
      Relation y g h d ∧ x ≫ d = (-f⟦(1 : ℤ)⟧') ≫ y := by
  rcases hx with ⟨Q, i, p, hTf, gbar, hg, hx⟩
  let Tf := Triangle.mk f i p
  have hTfi : Tf.rotate ∈ distTriang C := rot_of_distTriang Tf hTf
  obtain ⟨K, v, w, hTbar⟩ := distinguished_cocone_triangle gbar
  obtain ⟨Qg, j, q, hTg⟩ := distinguished_cocone_triangle g
  let Tbar := Triangle.mk gbar v w
  let Tg := Triangle.mk g j q
  let O := CategoryTheory.Triangulated.someOctahedron hg hTfi hTbar hTg
  dsimp only [Tf, Tbar, Tg, Triangle.mk, Triangle.rotate] at O
  have hpm : p ≫ O.m₁ = gbar ≫ j := by
    simpa [Tf, Tbar, Tg, O] using O.comm₁
  have hmq : O.m₁ ≫ q = -f⟦(1 : ℤ)⟧' := by
    exact O.comm₂
  have hgh : g ≫ h = 0 := (composable ⟨Q, i, p, hTf, gbar, hg, hx⟩).2
  obtain ⟨hbar₀, hhbar₀⟩ := Tg.yoneda_exact₂ hTg h hgh
  dsimp only [Tg, Triangle.mk] at hbar₀ hhbar₀
  let δ : X⟦(1 : ℤ)⟧ ⟶ W := x - O.m₁ ≫ hbar₀
  have hpδ : p ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hx, ← Category.assoc, hpm, Category.assoc,
      ← hhbar₀, sub_self]
  obtain ⟨a, ha⟩ := Tf.rotate.yoneda_exact₃ hTfi δ hpδ
  dsimp only [Tf, Triangle.mk, Triangle.rotate] at a ha
  let hbar : Qg ⟶ W := hbar₀ + q ≫ a
  have hjhbar : j ≫ hbar = h := by
    have hjq : j ≫ q = 0 := by
      have hzero := comp_distTriang_mor_zero₂₃ Tg hTg
      dsimp only [Tg, Triangle.mk] at hzero
      exact hzero
    dsimp [hbar]
    rw [Preadditive.comp_add, ← hhbar₀, ← Category.assoc, hjq, zero_comp, add_zero]
  have hmx : O.m₁ ≫ hbar = x := by
    dsimp [hbar]
    rw [Preadditive.comp_add, ← Category.assoc, hmq]
    rw [← ha]
    dsimp [δ]
    abel
  have hjhd : j ≫ (hbar ≫ d) = 0 := by
    rw [← Category.assoc, hjhbar, hhd]
  obtain ⟨y, hy⟩ := Tg.yoneda_exact₃ hTg (hbar ≫ d) hjhd
  dsimp only [Tg, Triangle.mk] at y hy
  refine ⟨y, ?_, ?_⟩
  · exact ⟨Qg, j, q, hTg, hbar, hjhbar, hy.symm⟩
  · calc
      x ≫ d = (O.m₁ ≫ hbar) ≫ d := by rw [hmx]
      _ = O.m₁ ≫ (hbar ≫ d) := Category.assoc _ _ _
      _ = O.m₁ ≫ (q ≫ y) := by rw [← hy]
      _ = (O.m₁ ≫ q) ≫ y := by rw [Category.assoc]
      _ = (-f⟦(1 : ℤ)⟧') ≫ y := by rw [hmq]

end

end KIP126.StableHomotopy.Toda
