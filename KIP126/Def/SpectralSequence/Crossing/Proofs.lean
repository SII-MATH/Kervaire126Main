module

import all KIP126.Def.SpectralSequence.Crossing.Predicates
public import KIP126.Def.SpectralSequence.Basic.Proofs
import all KIP126.Def.SpectralSequence.Basic.Proofs

@[expose] section

/-! Proofs about differential relations in the `SSData` model. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- The ambient differential relation is equivalent to compatible page representatives. -/
theorem dr_apply_iff_rel
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) :
    (∃ (x₀ : T ⟶ (E.ssData k).page
          (↑(r - E.r₀).toNat : WithTop ℕ))
        (y₀ : T ⟶ (E.ssData (k + E.diffDeg r)).page
          (↑(r - E.r₀).toNat : WithTop ℕ)),
      x₀ ≫ E.d r k = y₀ ∧
        ElementPageRel E r k x x₀ ∧
        ElementPageRel E r (k + E.diffDeg r) y y₀) ↔
      DifferentialRelation E r k x y := by
  constructor
  · rintro ⟨x₀, y₀, hxy, ⟨xZ, hxZ, hx₀⟩, ⟨yZ, hyZ, hy₀⟩⟩
    subst hx₀
    subst hy₀
    exact ⟨xZ, hxZ, yZ, hyZ, by rw [← Category.assoc]; exact hxy⟩
  · rintro ⟨xZ, hxZ, yZ, hyZ, hrel⟩
    exact ⟨
      xZ ≫ (E.ssData k).pageπ (↑(r - E.r₀).toNat : WithTop ℕ),
      yZ ≫ (E.ssData (k + E.diffDeg r)).pageπ
        (↑(r - E.r₀).toNat : WithTop ℕ),
      by rwa [Category.assoc],
      ⟨xZ, hxZ, rfl⟩,
      ⟨yZ, hyZ, rfl⟩⟩

/-- Targets of two differential relations with the same source differ by a page boundary. -/
theorem DifferentialRelation.targets_sub_factors_boundary
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) {T : C}
    {x : T ⟶ (E.ssData k).V}
    {y₁ y₂ : T ⟶ (E.ssData (k + E.diffDeg r)).V}
    (h₁ : DifferentialRelation E r k x y₁)
    (h₂ : DifferentialRelation E r k x y₂) :
    Subobject.Factors
      ((E.ssData (k + E.diffDeg r)).B (↑(r - E.r₀).toNat : WithTop ℕ))
      (y₁ - y₂) := by
  rcases h₁ with ⟨xZ₁, hx₁, yZ₁, hy₁, hrel₁⟩
  rcases h₂ with ⟨xZ₂, hx₂, yZ₂, hy₂, hrel₂⟩
  have heq : xZ₁ = xZ₂ := by
    apply (cancel_mono ((E.ssData k).Z (↑(r - E.r₀).toNat : WithTop ℕ)).arrow).mp
    exact hx₁.trans hx₂.symm
  subst xZ₂
  have hpage : yZ₁ ≫
      (E.ssData (k + E.diffDeg r)).pageπ (↑(r - E.r₀).toNat : WithTop ℕ) =
      yZ₂ ≫
      (E.ssData (k + E.diffDeg r)).pageπ (↑(r - E.r₀).toNat : WithTop ℕ) :=
    hrel₁.symm.trans hrel₂
  simpa only [hy₁, hy₂] using
    (E.ssData (k + E.diffDeg r)).sub_factors_boundary_of_page_eq
      (↑(r - E.r₀).toNat : WithTop ℕ) yZ₁ yZ₂ hpage

/-- An exact-target crossing is also a crossing with bounded target filtration. -/
theorem RelationCrossedByAt.toCrossed (E : SpectralSequence C ι)
    (filtDeg : ι → ℤ) (r : ℤ) (k : ι)
    {T : C} {x : T ⟶ (E.ssData k).V}
    {y : T ⟶ (E.ssData (k + E.diffDeg r)).V}
    {h : DifferentialRelation E r k x y}
    (hc : RelationCrossedByAt E filtDeg r k x y h) :
    RelationCrossedBy E filtDeg r k x y h := by
  rcases hc with ⟨a, ha, m, k', x', y', hs, he, ht⟩
  exact ⟨a, ha, m, k', x', y', hs, he, le_of_eq ht⟩

end KIP126.Core.SpectralSequence
