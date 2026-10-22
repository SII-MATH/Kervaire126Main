module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- A simultaneous family of finite-order cone attachments preserves an
actual order-realization homotopy model of the old space. The new model
is explicit and both comparison maps commute strictly with the old-space
comparisons, without assuming an order approximation of the attaching map. -/
theorem exists_orderSigmaConeAttachment_homotopyEquiv_of_model
    {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)] [∀ j, Fintype (P j)]
    (Q : Type u) [PartialOrder Q] {X T : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv |nerve Q| X)
    (a : SSet.toTop.obj (nerve (Σ j, P j)) ⟶ X)
    (u : X ⟶ T) (v : SSet.toTop.obj (nerve (Σ j, WithTop (P j))) ⟶ T)
    (hp : IsPushout a (SSet.toTop.map (nerveMap (orderSigmaConeEmbedding P).monotone.functor)) u v) :
    ∃ (n : ι → ℕ) (f : (Σ j, iteratedOrderSubdivision (P j) (n j + 1)) →o Q)
      (E : ContinuousMap.HomotopyEquiv
        |nerve (OrderSigmaConeAttachment (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f)| T),
      (∀ y : |nerve Q|, E (SSet.toTop.map (orderSigmaConeAttachmentTargetInclusion
        (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f) y) = u (e y)) ∧
      ∀ y : X, E.invFun (u y) = SSet.toTop.map
        (orderSigmaConeAttachmentTargetInclusion
          (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f) (e.invFun y) := by
  let b := a ≫ TopCat.ofHom e.invFun
  let i := SSet.toTop.map (nerveMap (orderSigmaConeEmbedding P).monotone.functor)
  have hb : IsPushout b i (pushout.inl b i) (pushout.inr b i) := IsPushout.of_hasPushout b i
  letI : Mono (nerveMap (orderSigmaConeEmbedding P).monotone.functor) :=
    nerveMap_mono_of_injective_orderHom (orderSigmaConeEmbedding P).toOrderHom
      (orderSigmaConeEmbedding P).injective
  obtain ⟨H⟩ := e.right_inv
  have H' : (e.toFun.comp b.hom).Homotopy a.hom :=
    H.comp (ContinuousMap.Homotopy.refl a.hom)
  obtain ⟨F,hF,hFinv⟩ := exists_homotopyEquiv_of_cofibration_pushout_homotopy_square
    hb hp (realization_mono_hasHomotopyExtension
      (nerveMap (orderSigmaConeEmbedding P).monotone.functor)) e H'
  obtain ⟨n,f,E,hE,hEinv⟩ := exists_orderSigmaConeAttachment_homotopyEquiv
    P Q b (pushout.inl b i) (pushout.inr b i) hb
  refine ⟨n,f,E.trans F,?_,?_⟩
  · intro y
    change F (E _) = _
    rw [hE]
    exact hF y
  · intro y
    change E.invFun (F.invFun (u y)) = _
    rw [hFinv]
    exact hEinv (e.invFun y)

end KIP126.Topology.SimplicialRealization
