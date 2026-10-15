module

public import KIP126.Def.Topology.Pushout.Collar.Data
public import KIP126.Def.Topology.Pushout.Representative
public import KIP126.Def.Topology.FiberBundle.Transport.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u v w

set_option backward.isDefEq.respectTransparency false

/-- Transport from the actual bundle over the collar neighborhood to
its old-space restriction, preserving the collar base coordinate. -/
noncomputable def attachmentCollarForward
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (c : AttachmentCollar i f a b)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.1.2) : c.Source p → c.Target p := by
  classical
  intro z
  by_cases hz : z.1.2.1 ∈ Set.range b
  · refine ⟨(z.1.1,z.1.2),?_⟩
    obtain ⟨y,hy⟩ := hz
    have hv : b y ∈ c.V := hy.symm ▸ z.1.2.2
    have hg : c.g z.1.2 = y :=
      (congrArg c.g (Subtype.ext hy)).symm.trans (c.g_b y hv)
    rw [hg]
    exact z.2.trans hy.symm
  · let x := pushoutCellRepresentative h z.1.2.1 hz
    have hx : a x = z.1.2.1 := pushoutCellRepresentative_projection h _ hz
    have hv : a x ∈ c.V := hx.symm ▸ z.1.2.2
    have hw : x ∈ c.W := by rw [← c.preimage_a]; exact hv
    let zx : {z : E × A // p z.1 = a z.2} := ⟨(z.1.1,x),z.2.trans hx.symm⟩
    refine ⟨(fiberChartTransport p a.hom e zx (i (c.r ⟨x,hw⟩)),z.1.2),?_⟩
    have hg : c.g z.1.2 = f (c.r ⟨x,hw⟩) :=
      (congrArg c.g (Subtype.ext hx)).symm.trans (c.g_a x hv)
    calc
      p (fiberChartTransport p a.hom e zx (i (c.r ⟨x,hw⟩))) =
          a (i (c.r ⟨x,hw⟩)) := fiberChartTransport_projection p a.hom e he _ _
      _ = b (f (c.r ⟨x,hw⟩)) := ConcreteCategory.congr_hom h.w _
      _ = b (c.g z.1.2) := congrArg b hg.symm

end KIP126.Topology
