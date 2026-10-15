module

public import KIP126.Def.Topology.Pushout.Collar.Data
public import KIP126.Def.Topology.Pushout.Representative
public import KIP126.Def.Topology.FiberBundle.Transport.Proofs

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

/-- The boundary lift of an old-fiber point in the actual cell product chart. -/
noncomputable def inverseBoundaryLift (t : c.Target p) (x : A) (hx : a x = t.val.2.val) :
    {z : E × A // p z.1 = a z.2} := by
  have hxV : a x ∈ c.V := hx ▸ t.val.2.property
  let xW : c.W := ⟨x,by rw [← c.preimage_a]; exact hxV⟩
  have hg : c.g t.val.2 = f (c.r xW) :=
    (congrArg c.g (Subtype.ext hx.symm)).trans (c.g_a x hxV)
  exact ⟨(t.val.1,i (c.r xW)),t.property.trans ((congrArg b hg).trans
    (ConcreteCategory.congr_hom h.w (c.r xW)).symm)⟩

/-- Transport from the boundary point over the collar retraction back to the
specified point of the cell, retaining the actual chart fiber coordinate. -/
noncomputable def inverseCellTransport (t : c.Target p) (x : A) (hx : a x = t.val.2.val) : E :=
  fiberChartTransport p a.hom e (c.inverseBoundaryLift h p t x hx) x

/-- The actual inverse collar transport, using the original point on the old
space and its unique cell representative elsewhere. -/
noncomputable def inverseTransport (t : c.Target p) : E := by
  classical
  exact if ht : t.val.2.val ∈ Set.range b then t.val.1 else
    c.inverseCellTransport h p e t (pushoutCellRepresentative h t.val.2.val ht)
      (pushoutCellRepresentative_projection h t.val.2.val ht)

end AttachmentCollar

/-- The actual inverse collar transport, retaining the specified neighborhood
coordinate as a point of the original bundle over that neighborhood. -/
noncomputable def attachmentCollarInverse
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (c : AttachmentCollar i f a b)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.val.2) : c.Target p → c.Source p :=
by
  classical
  intro t
  refine ⟨(c.inverseTransport h p e t,t.val.2),?_⟩
  by_cases ht : t.val.2.val ∈ Set.range b
  · simp only [AttachmentCollar.inverseTransport,dif_pos ht]
    obtain ⟨y,hy⟩ := ht
    have hg : c.g t.val.2 = y :=
      (congrArg c.g (Subtype.ext hy.symm)).trans (c.g_b y (hy ▸ t.val.2.property))
    exact t.property.trans ((congrArg b hg).trans hy)
  · simp only [AttachmentCollar.inverseTransport,dif_neg ht]
    exact (fiberChartTransport_projection p a.hom e he
      (c.inverseBoundaryLift h p t (pushoutCellRepresentative h t.val.2.val ht)
        (pushoutCellRepresentative_projection h t.val.2.val ht))
      (pushoutCellRepresentative h t.val.2.val ht)).trans
        (pushoutCellRepresentative_projection h t.val.2.val ht)

end KIP126.Topology
