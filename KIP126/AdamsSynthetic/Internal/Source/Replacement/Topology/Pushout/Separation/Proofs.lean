module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Cells.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- Attaching normal T1 cells along a closed embedded boundary preserves
the T1 property of the old space, even for an arbitrary attaching map. -/
theorem t1Space_of_topological_pushout
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A] [T1Space B]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) : T1Space P := by
  constructor
  intro p
  obtain (⟨y,rfl⟩ | ⟨x,rfl,hx⟩) :=
    Types.eq_or_eq_of_isPushout' (h.flip.map (forget TopCat)) p
  · change IsClosed ({b y} : Set P)
    have he : ({b y} : Set P) = b '' ({y} : Set B) := Set.image_singleton.symm
    rw [he]
    exact (isClosedEmbedding_of_topological_pushout h hi).isClosedMap _ isClosed_singleton
  · change IsClosed ({a x} : Set P)
    apply (isClosed_iff_of_topological_pushout h _).mpr
    constructor
    · have he : a ⁻¹' ({a x} : Set P) = {x} := by
        ext y
        exact ⟨fun hy => pushout_cell_eq_of_outside_boundary h hi hx hy.symm |>.symm,
          fun hy => congrArg a hy⟩
      rw [he]
      exact isClosed_singleton
    · have he : b ⁻¹' ({a x} : Set P) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨s,hs,_⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          (h.map (forget TopCat)).isColimit hi.injective x y).mp hy.symm
        exact hx ⟨s,hs⟩
      rw [he]
      exact isClosed_empty

/-- Arbitrary simultaneous normal T1 cell attachments preserve T1.
The coproduct and pushout are the actual specified attachment data. -/
theorem t1Space_of_attachCells {α : Type*} {A B : α → TopCat.{u}}
    [∀ i, NormalSpace (B i)] [∀ i, T1Space (B i)]
    {g : ∀ i, A i ⟶ B i} {X Y : TopCat.{u}} [T1Space X] {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u} g f)
    (hg : ∀ i, IsClosedEmbedding (g i)) : T1Space Y := by
  letI : NormalSpace (Σ i : c.ι, B (c.π i)) := normalSpace_sigma _
  letI : NormalSpace (TopCat.sigmaCofan (fun i : c.ι => B (c.π i))).pt :=
    inferInstanceAs (NormalSpace (Σ i : c.ι, B (c.π i)))
  letI : T1Space (TopCat.sigmaCofan (fun i : c.ι => B (c.π i))).pt :=
    inferInstanceAs (T1Space (Σ i : c.ι, B (c.π i)))
  let e := c.isColimit₂.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit (fun i : c.ι => B (c.π i)))
  letI : NormalSpace c.cofan₂.pt := (TopCat.homeoOfIso e).isClosedEmbedding.normalSpace
  letI : T1Space c.cofan₂.pt := (TopCat.homeoOfIso e).isEmbedding.t1Space
  exact t1Space_of_topological_pushout c.isPushout.flip
    (isClosedEmbedding_of_coproduct _ (fun i => hg (c.π i))
      _ _ c.isColimit₁ c.isColimit₂ c.m c.hm)

end KIP126.Topology
