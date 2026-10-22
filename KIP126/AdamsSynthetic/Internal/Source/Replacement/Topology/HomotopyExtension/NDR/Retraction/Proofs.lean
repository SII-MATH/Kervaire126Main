module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Retraction.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Homotopy.CompactParameter.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory Set _root_.Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- Neighborhood deformation data construct an actual cylinder retraction
onto the bottom and the specified subset cylinder. -/
theorem IsNDRData.exists_cylinder_retraction {X : Type*} [TopologicalSpace X]
    {S : Set X} {u : C(X,I)} {h : C(X × I,X)} (hN : IsNDRData S u h) :
    ∃ r : C(X × I, X × I),
      (∀ x, r (x,0) = (x,0)) ∧
      (∀ x ∈ S, ∀ t, r (x,t) = (x,t)) ∧
      (∀ q, (r q).2 = 0 ∨ (r q).1 ∈ S) := by
  let a : X × I → I := fun q => ⟨(q.2 : ℝ) / max (u q.1 : ℝ) (q.2 : ℝ), by
    constructor
    · exact div_nonneg q.2.property.1 (le_trans q.2.property.1 (le_max_right _ _))
    · by_cases hz : max (u q.1 : ℝ) (q.2 : ℝ) = 0
      · rw [hz,div_zero]; norm_num
      · exact (div_le_one (lt_of_le_of_ne
          (le_trans q.2.property.1 (le_max_right _ _)) (Ne.symm hz))).mpr (le_max_right _ _)⟩
  let b : C(X × I,I) := ⟨fun q => ⟨max 0 ((q.2 : ℝ) - u q.1), by
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      linarith [q.2.property.2,(u q.1).property.1]⟩,
    (continuous_const.max ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp (u.continuous.comp continuous_fst)))).subtype_mk (fun q =>
        ⟨le_max_left _ _, max_le (by norm_num) (by
          change (q.2 : ℝ) - (u q.1 : ℝ) ≤ 1
          linarith [q.2.property.2,(u q.1).property.1])⟩)⟩
  have hH : Continuous (fun q : X × I => h (q.1,a q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    by_cases hz : max (u q.1 : ℝ) (q.2 : ℝ) = 0
    · have hu : u q.1 = 0 := by
        apply Subtype.ext
        have := le_max_left (u q.1 : ℝ) (q.2 : ℝ)
        rw [hz] at this
        exact le_antisymm this (u q.1).property.1
      apply KIP126.Topology.Homotopy.continuousAt_comp_arbitrary_compact_parameter
        h Prod.fst a q continuous_fst.continuousAt
      intro t
      rw [hN.2.2.1 q.1 ((hN.1 q.1).mp hu),hN.2.2.1 q.1 ((hN.1 q.1).mp hu)]
    · have ha : ContinuousAt a q := by
        apply ContinuousAt.codRestrict
        exact continuous_snd.subtype_val.continuousAt.div
          ((u.continuous.comp continuous_fst).subtype_val.continuousAt.max
            continuous_snd.subtype_val.continuousAt) hz
      exact h.continuous.continuousAt.comp
        (continuous_fst.continuousAt.prodMk ha)
  let r : C(X × I,X × I) := ⟨fun q => (h (q.1,a q),b q), hH.prodMk b.continuous⟩
  refine ⟨r,?_,?_,?_⟩
  · intro x
    have ha : a (x,0) = 0 := by apply Subtype.ext; simp [a]
    have hb : b (x,0) = 0 := by
      apply Subtype.ext
      change max 0 (0-(u x : ℝ)) = 0
      exact max_eq_left (by linarith [(u x).property.1])
    change (h (x,a (x,0)),b (x,0)) = (x,0)
    rw [ha,hb,hN.2.1]
  · intro x hx t
    have hu := (hN.1 x).mpr hx
    have hb : b (x,t) = t := by apply Subtype.ext; simp [b,hu,t.property.1]
    change (h (x,a (x,t)),b (x,t)) = (x,t)
    rw [hN.2.2.1 x hx,hb]
  · intro q
    by_cases ht : (q.2 : ℝ) ≤ u q.1
    · left
      apply Subtype.ext
      change max 0 ((q.2 : ℝ) - u q.1) = 0
      exact max_eq_left (sub_nonpos.mpr ht)
    · right
      have hlt : (u q.1 : ℝ) < q.2 := lt_of_not_ge ht
      have hpos : (0 : ℝ) < q.2 := lt_of_le_of_lt (u q.1).property.1 hlt
      have ha : a q = 1 := by
        apply Subtype.ext
        change (q.2 : ℝ) / max (u q.1 : ℝ) (q.2 : ℝ) = 1
        rw [max_eq_right (le_of_lt hlt),div_self (ne_of_gt hpos)]
      change h (q.1,a q) ∈ S
      rw [ha]
      exact hN.2.2.2 q.1 (lt_of_lt_of_le hlt q.2.property.2)

/-- Actual NDR data on the image of a closed embedding supply full
homotopy extension for the original map. -/
theorem IsNDRData.hasHomotopyExtension {A B : TopCat} (i : A ⟶ B)
    (hi : IsClosedEmbedding i) {u : C(B,I)} {h : C(B × I,B)}
    (hN : IsNDRData (range i) u h) : HasHomotopyExtension i := by
  obtain ⟨r,h0,hside,hrange⟩ := hN.exists_cylinder_retraction
  exact hasHomotopyExtension_of_cylinder_retraction i hi r h0
    (fun a t => hside (i a) ⟨a,rfl⟩ t) hrange

end KIP126.Topology.HomotopyExtension
