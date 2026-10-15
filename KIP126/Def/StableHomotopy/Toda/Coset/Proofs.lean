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

/-- Every difference of representatives is a sum of the two actual indeterminacy terms. -/
theorem indeterminacy_complete {X Y Z W : C}
    {x₁ x₂ : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx₁ : Relation x₁ f g h) (hx₂ : Relation x₂ f g h) :
    ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
      x₁ - x₂ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := by
  rcases hx₁ with ⟨Q₁, i₁, p₁, hT₁, g₁, hg₁, hx₁⟩
  rcases hx₂ with ⟨Q₂, i₂, p₂, hT₂, g₂, hg₂, hx₂⟩
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f i₁ p₁) (Triangle.mk f i₂ p₂) hT₁ hT₂
    (𝟙 X) (𝟙 Y) (by
      change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp only [Category.comp_id, Category.id_comp])
  dsimp only [Triangle.mk] at c hc₁ hc₂
  have hi : i₁ ≫ c = i₂ := by simpa using hc₁
  have hp : p₁ = c ≫ p₂ := by simpa using hc₂
  let δ : Q₁ ⟶ Z := g₁ - c ≫ g₂
  have hδ : i₁ ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hg₁, ← Category.assoc, hi, hg₂, sub_self]
  obtain ⟨z, hz⟩ := (Triangle.mk f i₁ p₁).yoneda_exact₃ hT₁ δ hδ
  dsimp only [Triangle.mk] at z hz
  have hp₂x₂ : p₁ ≫ x₂ = (c ≫ g₂) ≫ h := by
    rw [hp, Category.assoc, hx₂, ← Category.assoc]
  have hpzh : p₁ ≫ (z ≫ h) = δ ≫ h := by
    rw [← Category.assoc, ← hz]
  let e : X⟦(1 : ℤ)⟧ ⟶ W := x₁ - x₂ - z ≫ h
  have he : p₁ ≫ e = 0 := by
    dsimp [e]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, hx₁, hp₂x₂, hpzh]
    dsimp [δ]
    rw [Preadditive.sub_comp]
    abel
  have hrot : (Triangle.mk f i₁ p₁).rotate ∈ distTriang C :=
    rot_of_distTriang (Triangle.mk f i₁ p₁) hT₁
  obtain ⟨y₀, hy₀⟩ := (Triangle.mk f i₁ p₁).rotate.yoneda_exact₃ hrot e he
  dsimp only [Triangle.mk, Triangle.rotate] at y₀ hy₀
  refine ⟨-y₀, z, ?_⟩
  have hy₀' : e = f⟦(1 : ℤ)⟧' ≫ (-y₀) := by
    simpa [Triangle.rotate] using hy₀
  calc
    x₁ - x₂ = e + z ≫ h := by dsimp [e]; abel
    _ = f⟦(1 : ℤ)⟧' ≫ (-y₀) + z ≫ h := by rw [hy₀']

/-- With any chosen representative as origin, the Toda bracket is exactly
its coset by the full left and right indeterminacy. No uniqueness or vanishing
of either indeterminacy term is assumed. -/
theorem relation_iff_indeterminacy {X Y Z W : C}
    {x₀ x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx₀ : Relation x₀ f g h) :
    Relation x f g h ↔
      ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
        x - x₀ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := by
  constructor
  · exact fun hx => indeterminacy_complete hx hx₀
  · rintro ⟨y, z, hx⟩
    have heq : x = (x₀ + f⟦(1 : ℤ)⟧' ≫ y) + z ≫ h := by
      calc
        x = (x - x₀) + x₀ := (sub_add_cancel x x₀).symm
        _ = (f⟦(1 : ℤ)⟧' ≫ y + z ≫ h) + x₀ := by rw [hx]
        _ = (x₀ + f⟦(1 : ℤ)⟧' ≫ y) + z ≫ h := by abel
    rw [heq]
    exact indeterminacy_right (indeterminacy_left hx₀ y) z

end

end KIP126.StableHomotopy.Toda
