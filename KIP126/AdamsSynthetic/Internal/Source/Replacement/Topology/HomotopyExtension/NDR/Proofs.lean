module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Retraction.Proofs
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.DenselyOrdered

@[expose] section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory Set _root_.Topology
open scoped unitInterval

universe u
set_option backward.isDefEq.respectTransparency false

/-- A closed homotopy-extension inclusion has an actual neighborhood
deformation, with zero set exactly its image. No metrizability or normality
of the original space is assumed. -/
theorem HasHomotopyExtension.exists_ndr {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : HasHomotopyExtension i) (he : IsClosedEmbedding i) :
    ∃ u : C(B, I), ∃ h : C(B × I, B),
      (∀ a, u (i a) = 0) ∧
      (∀ b, u b = 0 → b ∈ range i) ∧
      (∀ b, h (b, 0) = b) ∧
      (∀ a t, h (i a, t) = i a) ∧
      (∀ b, u b < 1 → h (b, 1) ∈ range i) := by
  obtain ⟨r,hr0,hri,hrange⟩ := hi.exists_cylinder_retraction
  let c : C(B, C(I, ℝ)) :=
    (⟨fun q : B × I => (q.2 : ℝ) - (r q).2,
      (continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp r.continuous.snd)⟩ : C(B × I, ℝ)).curry
  have hc (b : B) (t : I) : c b t = (t : ℝ) - (r (b,t)).2 := rfl
  have hnorm (b : B) : ‖c b‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).mpr
    intro t
    rw [hc, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(r (b,t)).2.property.1, (r (b,t)).2.property.2,
      t.property.1, t.property.2]
  let u : C(B,I) := ⟨fun b => ⟨‖c b‖, norm_nonneg _, hnorm b⟩,
    (continuous_norm.comp c.continuous).subtype_mk _⟩
  let h : C(B × I,B) := ⟨fun q => (r q).1, r.continuous.fst⟩
  refine ⟨u,h,?_,?_,?_,?_,?_⟩
  · intro a
    have ha : c (i a) = 0 := by
      ext t
      change (t : ℝ) - (r (i a,t)).2 = 0
      rw [hri]
      exact sub_self _
    apply Subtype.ext
    change ‖c (i a)‖ = 0
    rw [ha,norm_zero]
  · intro b hb
    have hz : c b = 0 := norm_eq_zero.mp (congrArg Subtype.val hb)
    have ht (t : I) : (r (b,t)).2 = t := by
      apply Subtype.ext
      have hc0 := congrArg (fun f : C(I,ℝ) => f t) hz
      change (t : ℝ) - (r (b,t)).2 = 0 at hc0
      linarith
    have hclosed : IsClosed {t : I | (r (b,t)).1 ∈ range i} :=
      he.isClosed_range.preimage (r.continuous.fst.comp (continuous_const.prodMk continuous_id))
    have hpos : Ioi (0 : I) ⊆ {t : I | (r (b,t)).1 ∈ range i} := by
      intro t ht0
      rcases hrange (b,t) with hzero | him
      · rw [ht] at hzero
        exact False.elim (ne_of_gt ht0 hzero)
      · exact him
    have hmem : (r (b,0)).1 ∈ range i :=
      (closure_minimal hpos hclosed) (show (0:I) ∈ closure (Ioi (0:I)) from by
        rw [closure_Ioi' (show (Ioi (0:I)).Nonempty from ⟨1, by norm_num⟩)]
        exact le_refl (0:I))
    simpa only [hr0] using hmem
  · intro b
    exact congrArg Prod.fst (hr0 b)
  · intro a t
    exact congrArg Prod.fst (hri a t)
  · intro b hb
    rcases hrange (b,1) with hz | him
    · have hn := (c b).norm_coe_le_norm (1 : I)
      rw [hc,hz] at hn
      norm_num at hn
      change ‖c b‖ < 1 at hb
      exact False.elim (not_lt_of_ge hn hb)
    · exact him

end KIP126.Topology.HomotopyExtension
