module

public import KIP126.Def.Topology.FiberBundle.Attachment.Forward.Proofs
public import KIP126.Def.Topology.FiberBundle.Attachment.Inverse.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u v w

set_option backward.isDefEq.respectTransparency false

variable {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
  {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
  (h : IsPushout i f a b) (hi : IsClosedEmbedding i) (c : AttachmentCollar i f a b)
  {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
  (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
  (he : ∀ z, (e z).2 = z.1.2)

include hi in
/-- Moving to the old fiber and back is the identity on the actual
bundle over the entire open collar neighborhood. -/
theorem attachmentCollarInverse_forward (z : c.Source p) :
    attachmentCollarInverse h c p e he (attachmentCollarForward h c p e he z) = z := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · change c.inverseTransport h p e (attachmentCollarForward h c p e he z) = z.1.1
    by_cases hz : z.1.2.1 ∈ Set.range b
    · rw [c.inverseTransport_old h p e _ (by simpa only [attachmentCollarForward_snd] using hz)]
      exact attachmentCollarForward_old h c p e he z hz
    · let x := pushoutCellRepresentative h z.1.2.1 hz
      have hx : a x = z.1.2.1 := pushoutCellRepresentative_projection h _ hz
      have hw : x ∈ c.W := by
        rw [← c.preimage_a]
        exact show a x ∈ c.V from hx.symm ▸ z.1.2.2
      let w := i (c.r ⟨x,hw⟩)
      let zx : {z : E × A // p z.1 = a z.2} := ⟨(z.1.1,x),z.2.trans hx.symm⟩
      rw [c.inverseTransport_cell h p e he hi (attachmentCollarForward h c p e he z) x
        (by simpa only [attachmentCollarForward_snd] using hx)]
      unfold AttachmentCollar.inverseCellTransport
      have hl : c.inverseBoundaryLift h p (attachmentCollarForward h c p e he z) x
          (by simpa only [attachmentCollarForward_snd] using hx) =
          ⟨(fiberChartTransport p a.hom e zx w,w),
            fiberChartTransport_projection p a.hom e he zx w⟩ := by
        apply Subtype.ext
        apply Prod.ext
        · exact attachmentCollarForward_cell h c p e he hi z x hx
        · rfl
      rw [hl,fiberChartTransport_trans p a.hom e he]
      exact fiberChartTransport_self p a.hom e he zx
  · simp only [attachmentCollarInverse_snd,attachmentCollarForward_snd]

include hi in
/-- Moving from the old fiber to the collar and back is the identity,
including the exact boundary-identification cases. -/
theorem attachmentCollarForward_inverse (t : c.Target p) :
    attachmentCollarForward h c p e he (attachmentCollarInverse h c p e he t) = t := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · by_cases ht : t.1.2.1 ∈ Set.range b
    · rw [attachmentCollarForward_old h c p e he _ (by simpa only [attachmentCollarInverse_snd] using ht)]
      exact c.inverseTransport_old h p e t ht
    · let x := pushoutCellRepresentative h t.1.2.1 ht
      have hx : a x = t.1.2.1 := pushoutCellRepresentative_projection h _ ht
      have hw : x ∈ c.W := by
        rw [← c.preimage_a]
        exact show a x ∈ c.V from hx.symm ▸ t.1.2.2
      let w := i (c.r ⟨x,hw⟩)
      let tx := c.inverseBoundaryLift h p t x hx
      rw [attachmentCollarForward_cell h c p e he hi (attachmentCollarInverse h c p e he t) x
        (by simpa only [attachmentCollarInverse_snd] using hx)]
      have hl : (⟨((attachmentCollarInverse h c p e he t).1.1,x),
          (attachmentCollarInverse h c p e he t).2.trans
            (by simpa only [attachmentCollarInverse_snd] using hx.symm)⟩ :
          {z : E × A // p z.1 = a z.2}) =
          ⟨(fiberChartTransport p a.hom e tx x,x),
            fiberChartTransport_projection p a.hom e he tx x⟩ := by
        apply Subtype.ext
        apply Prod.ext
        · exact c.inverseTransport_cell h p e he hi t x hx
        · rfl
      rw [hl,fiberChartTransport_trans p a.hom e he]
      exact fiberChartTransport_self p a.hom e he tx
  · simp only [attachmentCollarInverse_snd,attachmentCollarForward_snd]

end KIP126.Topology
