module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] public section

namespace KIP126.Foundation.CellAttachment

open _root_.CategoryTheory _root_.CategoryTheory.Limits HomotopicalAlgebra

universe w v u t

set_option backward.isDefEq.respectTransparency false

/-- Maps on an old space and its actual attached cells extend uniquely when
they agree on the original cell boundaries. -/
theorem exists_desc {C : Type u} [Category.{v} C]
    {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)
    {Z : C} (a : X ⟶ Z) (b : ∀ j, B (c.π j) ⟶ Z)
    (hb : ∀ j, c.cofan₁.inj j ≫ c.g₁ ≫ a = g (c.π j) ≫ b j) :
    ∃ d : Y ⟶ Z, f ≫ d = a ∧ ∀ j, c.cell j ≫ d = b j := by
  let q := Cofan.IsColimit.desc c.isColimit₂ b
  have hw : c.g₁ ≫ a = c.m ≫ q := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro j
    simpa only [c.hm_assoc, q, Cofan.IsColimit.fac] using hb j
  refine ⟨c.isPushout.desc a q hw, c.isPushout.inl_desc a q hw, ?_⟩
  intro j
  rw [AttachCells.cell_def, Category.assoc, c.isPushout.inr_desc]
  simp [q]

end KIP126.Foundation.CellAttachment
