module

public import KIP126.Def.Topology.FiberBundle.Pullback.Data
public import Mathlib.Topology.Homeomorph.Lemmas
public import KIP126.Def.Topology.FiberBundle.Chart.Proofs

@[expose] public section

section

namespace KIP126.Topology

variable {E A B : Type*} [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
set_option backward.isDefEq.respectTransparency false

/-- Along an embedding, restriction of the actual pullback is exactly
restriction of the original total space to the image of the base set. -/
noncomputable def pullbackEmbeddingRestrictionHomeomorph (p : C(E,B)) (a : C(A,B))
    (ha : _root_.Topology.IsEmbedding a) (U : Set A) :
    (pullbackSndMap p a ⁻¹' U) ≃ₜ (p ⁻¹' (a '' U)) := by
  let e := ha.homeomorphImage U
  let b : C(p ⁻¹' (a '' U),U) :=
    ⟨fun x => e.symm ⟨p x.val,x.property⟩,
      e.symm.continuous.comp ((p.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  have hb (x : p ⁻¹' (a '' U)) : a (b x).val = p x.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p x.val,x.property⟩)
  exact {
    toFun := fun z => ⟨z.val.val.1,⟨z.val.val.2,z.property,z.val.property.symm⟩⟩
    invFun := fun x => ⟨⟨(x.val,(b x).val),(hb x).symm⟩,(b x).property⟩
    left_inv := fun z => by
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rfl
      · exact ha.injective ((hb _).trans z.val.property)
    right_inv := fun _ => rfl
    continuous_toFun :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.prodMk (continuous_subtype_val.comp b.continuous)).subtype_mk _ |>.subtype_mk _ }

end KIP126.Topology

end

section

namespace KIP126.Topology

variable {E A B F : Type*} [TopologicalSpace E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

/-- A local chart over an open embedded base neighborhood gives an
actual local chart of the original projection. -/
theorem localTriviality_at_of_openEmbedding [Nonempty F]
    (p : C(E,B)) (a : C(A,B)) (ha : _root_.Topology.IsOpenEmbedding a)
    (x : A) (T : Bundle.Trivialization F (pullbackSndMap p a)) (hx : x ∈ T.baseSet) :
    ∃ T' : Bundle.Trivialization F p, a x ∈ T'.baseSet := by
  let e := pullbackEmbeddingRestrictionHomeomorph p a ha.isEmbedding T.baseSet
  let b := ha.isEmbedding.homeomorphImage T.baseSet
  let h := e.symm.trans ((T.preimageHomeomorph (Set.Subset.refl T.baseSet)).trans
    (b.prodCongr (Homeomorph.refl F)))
  have hh (z : p ⁻¹' (a '' T.baseSet)) : (h z).1.val = p z.val := by
    change (b (T.preimageHomeomorph (Set.Subset.refl T.baseSet) (e.symm z)).1).val = _
    rw [Bundle.Trivialization.preimageHomeomorph_apply]
    exact (e.symm z).val.property.symm
  obtain ⟨T',_,hT'⟩ := FiberBundle.exists_trivialization_at_of_open_product p (a '' T.baseSet)
    (ha.isOpenMap _ T.open_baseSet) h hh (a x) ⟨x,hx,rfl⟩
  exact ⟨T',hT'⟩

end KIP126.Topology

end
