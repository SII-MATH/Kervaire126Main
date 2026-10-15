module

public import KIP126.Def.CategoryTheory.CellAttachment.Extension.Proofs

@[expose] public section

namespace KIP126.Foundation.CellAttachment

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u t

set_option backward.isDefEq.respectTransparency false

/-- An actual pushout of one of the stated generators is an actual
one-cell attachment with that same target morphism. -/
theorem nonempty_of_isPushout {C : Type u} [Category.{v} C]
    {α : Type t} {A B : α → C} (g : ∀ i, A i ⟶ B i) (i : α)
    {X Y : C} (a : A i ⟶ X) (b : B i ⟶ Y) (f : X ⟶ Y)
    (h : IsPushout a (g i) f b) : Nonempty (AttachCells.{w} g f) := by
  refine ⟨{
    ι := PUnit.{w+1}
    π := fun _ => i
    cofan₁ := Cofan.mk (A i) (fun _ => 𝟙 _)
    cofan₂ := Cofan.mk (B i) (fun _ => 𝟙 _)
    isColimit₁ := Cofan.isColimitMkOfUnique (Iso.refl _) PUnit.{w+1}
    isColimit₂ := Cofan.isColimitMkOfUnique (Iso.refl _) PUnit.{w+1}
    m := g i
    hm := fun _ => by simp
    g₁ := a
    g₂ := b
    isPushout := h }⟩

/-- An original isomorphism is an attachment of the empty family; no
artificial cell is added to a padded or unchanged stage. -/
theorem nonempty_of_isIso {C : Type u} [Category.{v} C] [HasInitial C]
    {α : Type t} {A B : α → C} (g : ∀ i, A i ⟶ B i)
    {X Y : C} (f : X ⟶ Y) [IsIso f] : Nonempty (AttachCells.{w} g f) := by
  let π : PEmpty.{w+1} → α := PEmpty.elim
  let s (F : α → C) : Cofan (fun i => F (π i)) :=
    Cofan.mk (⊥_ C) (fun i => PEmpty.elim i)
  have hs (F : α → C) : IsColimit (s F) := by
    refine Cofan.IsColimit.mk _ (fun t => initial.to t.pt) ?_ ?_
    · intro t i
      exact PEmpty.elim i
    · intro t m hm
      exact initialIsInitial.hom_ext _ _
  refine ⟨{
    ι := PEmpty.{w+1}
    π := π
    cofan₁ := s A
    cofan₂ := s B
    isColimit₁ := hs A
    isColimit₂ := hs B
    m := 𝟙 (⊥_ C)
    hm := fun i => PEmpty.elim i
    g₁ := initial.to X
    g₂ := initial.to Y
    isPushout := by
      change IsPushout (initial.to X) (𝟙 (⊥_ C)) f (initial.to Y)
      exact IsPushout.of_vert_isIso ⟨initialIsInitial.hom_ext _ _⟩ }⟩

end KIP126.Foundation.CellAttachment
