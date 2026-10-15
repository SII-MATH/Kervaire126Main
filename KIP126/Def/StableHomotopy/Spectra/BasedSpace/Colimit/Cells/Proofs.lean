module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Colimit.Cells.Data
public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Colimit.Cells.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u w
variable {α : Type w} {A B : α → BasedSpace.{u}} {g : ∀ i, A i ⟶ B i}
  {X Y : BasedSpace.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)

set_option backward.isDefEq.respectTransparency false

/-- A based attachment is an actual topological pushout of the unbased
disjoint unions of its cells and their boundaries. -/
theorem attachment_isPushout :
    IsPushout (attachmentTop c) (attachmentLeft c)
      (forgetToTop.map f) (attachmentBottom c) := by
  apply IsPushout.mk'
  · apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    have h : (c.cofan₁.inj i ≫ c.g₁) ≫ f = g (c.π i) ≫ c.cell i := by
      rw [Category.assoc, c.isPushout.w, ← Category.assoc, c.hm i, Category.assoc]
      rfl
    exact congrArg (fun k => k.map x) h
  · intro T a b h₀ h₁
    have h : a.hom = b.hom := continuousMap_ext_of_attachCells c T a.hom b.hom
      (congrArg TopCat.Hom.hom h₀) (fun i => by
        apply ContinuousMap.ext
        intro x
        exact ConcreteCategory.congr_hom h₁ ⟨i,x⟩)
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k => k x) h
  · intro T a b h
    let bs (i : c.ι) : C(B (c.π i),T) :=
      b.hom.comp (TopCat.sigmaι (fun j => (B (c.π j)).space) i).hom
    obtain ⟨l,hl,hl'⟩ := exists_continuous_desc_of_attachCells c T a.hom bs
      (fun i x => ConcreteCategory.congr_hom h ⟨i,x⟩)
    refine ⟨TopCat.ofHom l, ?_, ?_⟩
    · apply ConcreteCategory.hom_ext
      intro x
      exact congrArg (fun k => k x) hl
    · apply ConcreteCategory.hom_ext
      rintro ⟨i,x⟩
      exact congrArg (fun k => k x) (hl' i)

/-- Forgetting the point preserves an actual cell attachment with its
same indexing family, even though it does not preserve coproducts alone. -/
noncomputable def attachCells_forgetToTop :
    AttachCells.{u} (fun i => forgetToTop.map (g i)) (forgetToTop.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := TopCat.sigmaCofan (fun i => (A (c.π i)).space)
  cofan₂ := TopCat.sigmaCofan (fun i => (B (c.π i)).space)
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := attachmentLeft c
  hm i := rfl
  g₁ := attachmentTop c
  g₂ := attachmentBottom c
  isPushout := attachment_isPushout c

end KIP126.StableHomotopy.Spectra.BasedSpace
