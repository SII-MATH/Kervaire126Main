module

public import KIP126.Def.Topology.FiberBundle.Attachment.Compatibility.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u v w

/-- The actual bundle over a disk-attachment collar is homeomorphic to
the old bundle pulled back along the concrete collar retraction. -/
noncomputable def attachmentCollarHomeomorph
    {S A B P : TopCat.{u}} [CompactSpace A] [CompactSpace B] [T2Space P]
    [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) (c : AttachmentCollar i f a b)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.val.2) : c.Source p ≃ₜ c.Target p where
  toFun := attachmentCollarForward h c p e he
  invFun := attachmentCollarInverse h c p e he
  left_inv := attachmentCollarInverse_forward h hi c p e he
  right_inv := attachmentCollarForward_inverse h hi c p e he
  continuous_toFun := attachmentCollarForward_continuous h c p e he hi
  continuous_invFun := attachmentCollarInverse_continuous h hi c p e he

end KIP126.Topology
