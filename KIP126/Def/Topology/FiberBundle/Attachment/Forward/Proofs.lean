module

public import KIP126.Def.Topology.FiberBundle.Attachment.Forward.Data
public import KIP126.Def.Topology.Pushout.Compact.Descent.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u v w

set_option backward.isDefEq.respectTransparency false

variable {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
  (h : IsPushout i f a b) (c : AttachmentCollar i f a b)
  {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
  (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
  (he : ∀ z, (e z).2 = z.1.2)

@[simp] theorem attachmentCollarForward_snd (z : c.Source p) :
    (attachmentCollarForward h c p e he z).1.2 = z.1.2 := by
  classical
  by_cases hz : z.1.2.1 ∈ Set.range b <;> simp [attachmentCollarForward,hz]

/-- Forward transport fixes points over the actual old-space image. -/
theorem attachmentCollarForward_old (z : c.Source p) (hz : z.1.2.1 ∈ Set.range b) :
    (attachmentCollarForward h c p e he z).1.1 = z.1.1 := by
  classical
  simp [attachmentCollarForward,hz]

/-- The single cell-coordinate formula for forward transport remains
valid on the attaching boundary, where it agrees with the old-space map. -/
theorem attachmentCollarForward_cell [NormalSpace A] [T1Space A]
    (hi : IsClosedEmbedding i) (z : c.Source p) (x : A) (hx : a x = z.1.2.1) :
    (attachmentCollarForward h c p e he z).1.1 =
      fiberChartTransport p a.hom e ⟨(z.1.1,x),z.2.trans hx.symm⟩
        (i (c.r ⟨x,by rw [← c.preimage_a]; exact show a x ∈ c.V from hx.symm ▸ z.1.2.2⟩)) := by
  classical
  by_cases hz : z.1.2.1 ∈ Set.range b
  · rw [attachmentCollarForward_old h c p e he z hz]
    obtain ⟨y,hy⟩ := hz
    obtain ⟨s,hs,_⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (h.map (forget TopCat)).isColimit hi.injective x y).mp (hx.trans hy.symm)
    have hr : c.r ⟨x,by rw [← c.preimage_a]; exact show a x ∈ c.V from hx.symm ▸ z.1.2.2⟩ = s := by
      subst x
      exact c.r_i s
    have hir : i (c.r ⟨x,by rw [← c.preimage_a]; exact show a x ∈ c.V from hx.symm ▸ z.1.2.2⟩) = x :=
      (congrArg i hr).trans hs
    rw [hir]
    exact (fiberChartTransport_self p a.hom e he ⟨(z.1.1,x),z.2.trans hx.symm⟩).symm
  · have hr := pushoutCellRepresentative_eq h hi z.1.2.1 hz x hx
    simp only [attachmentCollarForward,dif_neg hz]
    simp only [hr]

/-- The actual forward collar transport is continuous. The proof descends
from both compact attachment pieces, including all boundary identifications. -/
theorem attachmentCollarForward_continuous [CompactSpace A] [CompactSpace B]
    [T2Space P] [NormalSpace A] [T1Space A] (hi : IsClosedEmbedding i) :
    Continuous (attachmentCollarForward h c p e he) := by
  let k : C(c.Source p,P) :=
    ⟨fun z => z.1.2.1,continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  have hm : Continuous (fun z : c.Source p => (attachmentCollarForward h c p e he z).1.1) := by
    apply continuous_of_compact_pushout_pullback h k
    · let T := {zt : A × c.Source p // a zt.1 = k zt.2}
      let zx : T → {z : E × A // p z.1 = a z.2} :=
        fun t => ⟨(t.1.2.1.1,t.1.1),t.1.2.2.trans t.2.symm⟩
      have hzx : Continuous zx := by
        exact ((continuous_fst.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).prodMk
          (continuous_fst.comp continuous_subtype_val)).subtype_mk _
      let wx : T → c.W := fun t => ⟨t.1.1,by
        rw [← c.preimage_a]
        exact show a t.1.1 ∈ c.V from t.2.symm ▸ t.1.2.1.2.2⟩
      have hwx : Continuous wx := (continuous_fst.comp continuous_subtype_val).subtype_mk _
      have ht := (fiberChartTransport_continuous p a.hom e).comp
        (hzx.prodMk (i.hom.continuous.comp (c.r.continuous.comp hwx)))
      apply ht.congr
      intro t
      exact (attachmentCollarForward_cell h c p e he hi t.1.2 t.1.1 t.2).symm
    · have heq : (fun t : {zt : B × c.Source p // b zt.1 = k zt.2} =>
          (attachmentCollarForward h c p e he t.1.2).1.1) = fun t => t.1.2.1.1 := by
        funext t
        exact attachmentCollarForward_old h c p e he t.1.2 ⟨t.1.1,t.2⟩
      rw [heq]
      exact continuous_fst.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))
  have hs : Continuous (fun z : c.Source p => (attachmentCollarForward h c p e he z).1.2) := by
    simp only [attachmentCollarForward_snd]
    exact continuous_snd.comp continuous_subtype_val
  exact (hm.prodMk hs).subtype_mk _

end KIP126.Topology
