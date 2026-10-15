module

public import KIP126.Def.Topology.HomotopyExtension.NDR.Product.Data
public import KIP126.Def.Topology.Homotopy.CompactParameter.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open Set _root_.Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

private theorem relativeTime_continuousAt {Z : Type*} [TopologicalSpace Z]
    (r s t : Z → I) (z : Z) (hr : ContinuousAt r z) (hs : ContinuousAt s z)
    (ht : ContinuousAt t z) (hn : max (r z : ℝ) (s z : ℝ) ≠ 0) :
    ContinuousAt (fun w => ndrRelativeTime (r w) (s w) (t w)) z := by
  apply ContinuousAt.codRestrict
  have hr' := continuous_subtype_val.continuousAt.comp hr
  have hs' := continuous_subtype_val.continuousAt.comp hs
  have ht' := continuous_subtype_val.continuousAt.comp ht
  exact ht'.mul (hs'.div (hr'.max hs') hn)

/-- Actual neighborhood deformations are preserved by the union product
pair. No separation condition on either ambient space is used. -/
theorem IsNDRData.exists_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} {u : C(X,I)} {v : C(Y,I)}
    {h : C(X × I,X)} {k : C(Y × I,Y)}
    (hN : IsNDRData S u h) (kN : IsNDRData T v k) :
    ∃ w : C(X × Y,I), ∃ H : C((X × Y) × I,X × Y),
      IsNDRData {q | q.1 ∈ S ∨ q.2 ∈ T} w H := by
  let w : C(X × Y,I) := ⟨fun q => ⟨(u q.1 : ℝ) * (v q.2 : ℝ),
    mul_nonneg (u q.1).property.1 (v q.2).property.1,
    by nlinarith [(u q.1).property.1,(u q.1).property.2,
      (v q.2).property.1,(v q.2).property.2]⟩,
    ((u.continuous.comp continuous_fst).subtype_val.mul
      (v.continuous.comp continuous_snd).subtype_val).subtype_mk _⟩
  let a : (X × Y) × I → I := fun q => ndrRelativeTime (u q.1.1) (v q.1.2) q.2
  let b : (X × Y) × I → I := fun q => ndrRelativeTime (v q.1.2) (u q.1.1) q.2
  have hz_u (q : (X × Y) × I) (hz : max (u q.1.1 : ℝ) (v q.1.2 : ℝ) = 0) :
      u q.1.1 = 0 := by
    apply Subtype.ext
    change (u q.1.1 : ℝ) = 0
    exact le_antisymm (by rw [← hz]; exact le_max_left _ _)
      (u q.1.1).property.1
  have hz_v (q : (X × Y) × I) (hz : max (u q.1.1 : ℝ) (v q.1.2 : ℝ) = 0) :
      v q.1.2 = 0 := by
    apply Subtype.ext
    change (v q.1.2 : ℝ) = 0
    exact le_antisymm (by rw [← hz]; exact le_max_right _ _)
      (v q.1.2).property.1
  have ha : Continuous (fun q : (X × Y) × I => h (q.1.1,a q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    by_cases hz : max (u q.1.1 : ℝ) (v q.1.2 : ℝ) = 0
    · apply KIP126.Topology.Homotopy.continuousAt_comp_arbitrary_compact_parameter
        h (fun q => q.1.1) a q continuous_fst.fst.continuousAt
      intro t
      rw [hN.2.2.1 _ ((hN.1 _).mp (hz_u q hz)), hN.2.2.1 _ ((hN.1 _).mp (hz_u q hz))]
    · exact h.continuous.continuousAt.comp (continuous_fst.fst.continuousAt.prodMk
        (relativeTime_continuousAt _ _ _ q
          (u.continuous.comp continuous_fst.fst).continuousAt
          (v.continuous.comp continuous_fst.snd).continuousAt continuous_snd.continuousAt hz))
  have hb : Continuous (fun q : (X × Y) × I => k (q.1.2,b q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    by_cases hz : max (u q.1.1 : ℝ) (v q.1.2 : ℝ) = 0
    · apply KIP126.Topology.Homotopy.continuousAt_comp_arbitrary_compact_parameter
        k (fun q => q.1.2) b q continuous_fst.snd.continuousAt
      intro t
      rw [kN.2.2.1 _ ((kN.1 _).mp (hz_v q hz)), kN.2.2.1 _ ((kN.1 _).mp (hz_v q hz))]
    · exact k.continuous.continuousAt.comp (continuous_fst.snd.continuousAt.prodMk
        (relativeTime_continuousAt _ _ _ q
          (v.continuous.comp continuous_fst.snd).continuousAt
          (u.continuous.comp continuous_fst.fst).continuousAt continuous_snd.continuousAt
          (by rwa [max_comm])))
  let H : C((X × Y) × I,X × Y) := ⟨fun q => (h (q.1.1,a q), k (q.1.2,b q)),ha.prodMk hb⟩
  refine ⟨w,H,?_,?_,?_,?_⟩
  · intro q
    have hu : (u q.1 : ℝ) = 0 ↔ q.1 ∈ S := by
      rw [← hN.1 q.1]
      exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    have hv : (v q.2 : ℝ) = 0 ↔ q.2 ∈ T := by
      rw [← kN.1 q.2]
      exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    rw [Subtype.ext_iff]
    change (u q.1 : ℝ) * (v q.2 : ℝ) = 0 ↔ _
    rw [mul_eq_zero,hu,hv]
    rfl
  · intro q
    have az : a (q,0) = 0 := by apply Subtype.ext; simp [a,ndrRelativeTime]
    have bz : b (q,0) = 0 := by apply Subtype.ext; simp [b,ndrRelativeTime]
    change (h (q.1,a (q,0)),k (q.2,b (q,0))) = q
    rw [az,bz,hN.2.1,kN.2.1]
  · intro q hq t
    rcases hq with hq | hq
    · have bz : b (q,t) = 0 := by
        apply Subtype.ext
        simp [b,ndrRelativeTime,(hN.1 _).mpr hq]
      change (h (q.1,a (q,t)),k (q.2,b (q,t))) = q
      rw [hN.2.2.1 _ hq,bz,kN.2.1]
    · have az : a (q,t) = 0 := by
        apply Subtype.ext
        simp [a,ndrRelativeTime,(kN.1 _).mpr hq]
      change (h (q.1,a (q,t)),k (q.2,b (q,t))) = q
      rw [kN.2.2.1 _ hq,az,hN.2.1]
  · intro q hw
    change (u q.1 : ℝ) * (v q.2 : ℝ) < 1 at hw
    change h (q.1,a (q,1)) ∈ S ∨ k (q.2,b (q,1)) ∈ T
    by_cases huv : (u q.1 : ℝ) ≤ v q.2
    · left
      by_cases hvz : v q.2 = 0
      · have huz : u q.1 = 0 := by
          apply Subtype.ext
          rw [hvz] at huv
          exact le_antisymm huv (u q.1).property.1
        rw [hN.2.2.1 _ ((hN.1 _).mp huz)]
        exact (hN.1 _).mp huz
      · have av : a (q,1) = 1 := by
          apply Subtype.ext
          change (1 : ℝ) * ((v q.2 : ℝ) / max (u q.1 : ℝ) (v q.2 : ℝ)) = 1
          rw [max_eq_right huv,div_self (by exact fun h => hvz (Subtype.ext h)),one_mul]
        rw [av]
        apply hN.2.2.2
        change (u q.1 : ℝ) < 1
        nlinarith [(u q.1).property.1,(u q.1).property.2,(v q.2).property.2]
    · right
      have hvu := le_of_lt (lt_of_not_ge huv)
      have huz : (u q.1 : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt (v q.2).property.1 (lt_of_not_ge huv))
      have bv : b (q,1) = 1 := by
        apply Subtype.ext
        change (1 : ℝ) * ((u q.1 : ℝ) / max (v q.2 : ℝ) (u q.1 : ℝ)) = 1
        rw [max_eq_right hvu,div_self huz,one_mul]
      rw [bv]
      exact kN.2.2.2 _ (lt_of_lt_of_le (lt_of_not_ge huv) (u q.1).property.2)

end KIP126.Topology.HomotopyExtension
