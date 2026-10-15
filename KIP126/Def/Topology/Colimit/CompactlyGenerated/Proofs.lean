module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import KIP126.Def.Topology.Pushout.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- An actual topological colimit of compactly generated spaces is
compactly generated; the original compact Hausdorff test universe is kept. -/
theorem uCompactlyGeneratedSpace_of_isColimit
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{u} (F.obj j)] :
    UCompactlyGeneratedSpace.{u} c.pt := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  apply (TopCat.continuous_iff_of_isColimit c hc _).mpr
  intro j
  apply continuous_from_uCompactlyGeneratedSpace
  intro S g
  exact hf S ((c.ι.app j).hom.comp g)

/-- A topological pushout is compactly generated when its two target
pieces are; no extra condition on their common source is needed. -/
theorem uCompactlyGeneratedSpace_of_topological_pushout
    {S A B P : TopCat.{u}} [UCompactlyGeneratedSpace.{u} A]
    [UCompactlyGeneratedSpace.{u} B]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) : UCompactlyGeneratedSpace.{u} P := by
  apply uCompactlyGeneratedSpace_of_isClosed
  intro K hK
  apply (isClosed_iff_of_topological_pushout h K).mpr
  constructor
  · exact UCompactlyGeneratedSpace.isClosed (fun S g => hK S (a.hom.comp g))
  · exact UCompactlyGeneratedSpace.isClosed (fun S g => hK S (b.hom.comp g))

/-- Attaching any family of compactly generated cells preserves compact
generation of the old space. -/
theorem uCompactlyGeneratedSpace_of_attachCells
    {α : Type*} {A B : α → TopCat.{u}}
    [∀ i, UCompactlyGeneratedSpace.{u} (B i)]
    {g : ∀ i, A i ⟶ B i} {X Y : TopCat.{u}}
    [UCompactlyGeneratedSpace.{u} X] {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u} g f) :
    UCompactlyGeneratedSpace.{u} Y := by
  letI (i : Discrete c.ι) : UCompactlyGeneratedSpace.{u}
      ((Discrete.functor (fun i => B (c.π i))).obj i) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{u} (B (c.π i.as)))
  letI : UCompactlyGeneratedSpace.{u} c.cofan₂.pt :=
    uCompactlyGeneratedSpace_of_isColimit _ c.cofan₂ c.isColimit₂
  exact uCompactlyGeneratedSpace_of_topological_pushout c.isPushout

end KIP126.Topology
