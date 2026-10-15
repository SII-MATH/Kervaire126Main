module

public import KIP126.Def.Topology.FiberBundle.Attachment.Inverse.Data
public import KIP126.Def.Topology.Pushout.Compact.Descent.Proofs

@[expose] public section

namespace KIP126.Topology
open CategoryTheory CategoryTheory.Limits _root_.Topology Set
universe u v w
set_option backward.isDefEq.respectTransparency false

namespace AttachmentCollar
variable {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
  (c : AttachmentCollar i f a b) (h : IsPushout i f a b)
  {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
  (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))

variable (he : ∀ z, (e z).2 = z.val.2)

include he in
theorem inverseCellTransport_boundary (t : c.Target p) (s : S) (hs : a (i s) = t.val.2.val) :
    c.inverseCellTransport h p e t (i s) hs = t.val.1 := by
  unfold inverseCellTransport inverseBoundaryLift
  dsimp only
  simp only [c.r_i]
  exact fiberChartTransport_self p a.hom e he _

theorem inverseTransport_old (t : c.Target p) (ht : t.val.2.val ∈ Set.range b) :
    c.inverseTransport h p e t = t.val.1 := by
  classical
  simp only [inverseTransport,dif_pos ht]

include he in
/-- On every cell representative, including boundary representatives,
the actual inverse is exactly the continuous chart-transport formula. -/
theorem inverseTransport_cell [NormalSpace A] [T1Space A]
    (hi : IsClosedEmbedding i) (t : c.Target p) (x : A) (hx : a x = t.val.2.val) :
    c.inverseTransport h p e t = c.inverseCellTransport h p e t x hx := by
  classical
  by_cases ht : t.val.2.val ∈ Set.range b
  · rw [c.inverseTransport_old h p e t ht]
    obtain ⟨y,hy⟩ := ht
    obtain ⟨s,hs,_⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit (h.map (forget TopCat)).isColimit
        hi.injective x y).mp (hx.trans hy.symm)
    subst x
    exact (c.inverseCellTransport_boundary h p e he t s hx).symm
  · dsimp only [inverseTransport]
    rw [dif_neg ht]
    have hx' := pushoutCellRepresentative_eq h hi t.val.2.val ht x hx
    subst x
    rfl

/-- The boundary lift is jointly continuous on the actual cell pullback. -/
theorem inverseBoundaryLift_continuous :
    Continuous (fun z : {z : A × c.Target p // a z.1 = z.2.val.2.val} =>
      c.inverseBoundaryLift h p z.val.2 z.val.1 z.property) := by
  let D := {z : A × c.Target p // a z.1 = z.2.val.2.val}
  have hv (z : D) : z.val.1 ∈ c.W := by
    rw [← c.preimage_a]
    change a z.val.1 ∈ c.V
    rw [z.property]
    exact z.val.2.val.2.property
  have hw : Continuous (fun z : D => (⟨z.val.1,hv z⟩ : c.W)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hE : Continuous (fun z : D => z.val.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
  exact (hE.prodMk (i.hom.continuous.comp (c.r.continuous.comp hw))).subtype_mk _

/-- Transport back to the cell is jointly continuous, including on its boundary. -/
theorem inverseCellTransport_continuous :
    Continuous (fun z : {z : A × c.Target p // a z.1 = z.2.val.2.val} =>
      c.inverseCellTransport h p e z.val.2 z.val.1 z.property) :=
  (fiberChartTransport_continuous p a.hom e).comp
    ((c.inverseBoundaryLift_continuous h p).prodMk (continuous_fst.comp continuous_subtype_val))

include he in
/-- The actual inverse collar transport is continuous by descent through the
two proper pullback maps of the compact attachment. -/
theorem inverseTransport_continuous [CompactSpace A] [CompactSpace B] [T2Space P]
    [NormalSpace A] [T1Space A] (hi : IsClosedEmbedding i) :
    Continuous (c.inverseTransport h p e) := by
  let k : C(c.Target p,P) := ⟨fun t => t.val.2.val,
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  apply continuous_of_compact_pushout_pullback h k (c.inverseTransport h p e)
  · have heq : (fun z : {z : A × c.Target p // a z.1 = k z.2} =>
        c.inverseTransport h p e z.val.2) =
        (fun z => c.inverseCellTransport h p e z.val.2 z.val.1 z.property) := by
      funext z
      exact c.inverseTransport_cell h p e he hi z.val.2 z.val.1 z.property
    rw [heq]
    exact c.inverseCellTransport_continuous h p e
  · have heq : (fun z : {z : B × c.Target p // b z.1 = k z.2} =>
        c.inverseTransport h p e z.val.2) = (fun z => z.val.2.val.1) := by
      funext z
      exact c.inverseTransport_old h p e z.val.2 ⟨z.val.1,z.property⟩
    rw [heq]
    exact continuous_fst.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

end AttachmentCollar

@[simp] theorem attachmentCollarInverse_snd
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (c : AttachmentCollar i f a b)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.val.2) (t : c.Target p) :
    (attachmentCollarInverse h c p e he t).val.2 = t.val.2 := rfl

theorem attachmentCollarInverse_continuous
    {S A B P : TopCat.{u}} [CompactSpace A] [CompactSpace B] [T2Space P]
    [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) (c : AttachmentCollar i f a b)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.val.2) : Continuous (attachmentCollarInverse h c p e he) :=
  ((c.inverseTransport_continuous h p e he hi).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

end KIP126.Topology
