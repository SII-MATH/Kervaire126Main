module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]

/-- Every continuous map between actual finite order realizations extends
continuously over the actual order cones, preserving the cone height. -/
theorem exists_orderConeMap [Nonempty P] (g : C(|nerve P|, |nerve Q|)) :
    ∃ G : C(|nerve (WithTop P)|, |nerve (WithTop Q)|),
      ∀ (t : I) (x : |nerve P|),
        G (orderConeParameter P (t, x)) = orderConeParameter Q (t, g x) := by
  let a : C(I × |nerve P|, |nerve (WithTop Q)|) :=
    ⟨fun z => orderConeParameter Q (z.1, g z.2),
      (orderConeParameter Q).continuous.comp (continuous_fst.prodMk
        (g.continuous.comp continuous_snd))⟩
  have ha (z z' : I × |nerve P|)
      (hz : orderConeParameter P z = orderConeParameter P z') : a z = a z' := by
    obtain ⟨ht, hx⟩ := (orderConeParameter_eq_iff P z.1 z'.1 z.2 z'.2).mp hz
    apply (orderConeParameter_eq_iff Q z.1 z'.1 (g z.2) (g z'.2)).mpr
    exact ⟨ht, hx.imp id (congrArg g)⟩
  let G : |nerve (WithTop P)| → |nerve (WithTop Q)| :=
    fun z => a (Function.surjInv (orderConeParameter_surjective P) z)
  have hG (t : I) (x : |nerve P|) :
      G (orderConeParameter P (t, x)) = orderConeParameter Q (t, g x) := by
    exact ha (Function.surjInv (orderConeParameter_surjective P) _) (t, x)
      (Function.surjInv_eq (orderConeParameter_surjective P) _)
  have hcont : Continuous G := by
    apply (orderConeParameter_isQuotientMap P).continuous_iff.mpr
    have he : G ∘ orderConeParameter P = a := funext fun z => hG z.1 z.2
    rw [he]
    exact a.continuous
  exact ⟨⟨G, hcont⟩, hG⟩

/-- An actual homeomorphism of finite nonempty order realizations extends
to an actual homeomorphism of their order cones. It preserves height,
extends the given base homeomorphism strictly, and takes apex to apex. -/
theorem exists_orderCone_homeomorph [Nonempty P] [Nonempty Q]
    (h : |nerve P| ≃ₜ |nerve Q|) :
    ∃ e : |nerve (WithTop P)| ≃ₜ |nerve (WithTop Q)|,
      (∀ (t : I) (x : |nerve P|),
        e (orderConeParameter P (t, x)) = orderConeParameter Q (t, h x)) ∧
      (∀ x : |nerve P|,
        e (SSet.toTop.map (orderMappingConeSourceTopInclusion P) x) =
          SSet.toTop.map (orderMappingConeSourceTopInclusion Q) (h x)) ∧
      e (orderVertex (WithTop P) ⊤) = orderVertex (WithTop Q) ⊤ := by
  obtain ⟨F, hF⟩ := exists_orderConeMap (⟨h, h.continuous⟩ : C(|nerve P|, |nerve Q|))
  obtain ⟨G, hG⟩ := exists_orderConeMap (⟨h.symm, h.symm.continuous⟩ : C(|nerve Q|, |nerve P|))
  change ∀ (t : I) (x : |nerve P|),
    F (orderConeParameter P (t, x)) = orderConeParameter Q (t, h x) at hF
  change ∀ (t : I) (x : |nerve Q|),
    G (orderConeParameter Q (t, x)) = orderConeParameter P (t, h.symm x) at hG
  let e : |nerve (WithTop P)| ≃ₜ |nerve (WithTop Q)| :=
    { toFun := F
      invFun := G
      left_inv := by
        intro z
        obtain ⟨⟨t, x⟩, rfl⟩ := orderConeParameter_surjective P z
        rw [hF, hG]
        exact congrArg (fun x => orderConeParameter P (t, x)) (h.symm_apply_apply x)
      right_inv := by
        intro z
        obtain ⟨⟨t, x⟩, rfl⟩ := orderConeParameter_surjective Q z
        rw [hG, hF]
        exact congrArg (fun x => orderConeParameter Q (t, x)) (h.apply_symm_apply x)
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  refine ⟨e, hF, ?_, ?_⟩
  · intro x
    change F _ = _
    simpa only [orderConeParameter_zero] using hF 0 x
  · change F _ = _
    simpa only [orderConeParameter_one] using
      hF 1 (orderVertex P (Classical.arbitrary P))

end KIP126.Topology.SimplicialRealization
