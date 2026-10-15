module

public import KIP126.Def.Topology.Simplex.Combination.Proofs
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology.Simplex

open scoped unitInterval

/-- Two continuous simplex-valued maps are joined by their actual
straight-line homotopy, with its coordinate formula retained. -/
theorem exists_affine_homotopy {X V : Type*} [TopologicalSpace X] [Fintype V]
    (a b : C(X,stdSimplex ℝ V)) :
    ∃ H : a.Homotopy b, ∀ (t : I) (x : X) (j : V),
      H (t,x) j = (1 - (t : ℝ)) * a x j + (t : ℝ) * b x j := by
  let h (z : I × X) (j : V) : ℝ :=
    (1 - (z.1 : ℝ)) * a z.2 j + (z.1 : ℝ) * b z.2 j
  have hn (z) (j) : 0 ≤ h z j :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) ((a z.2).property.1 j))
      (mul_nonneg z.1.property.1 ((b z.2).property.1 j))
  have hs (z) : ∑ j, h z j = 1 := by
    simp only [h,Finset.sum_add_distrib,← Finset.mul_sum,stdSimplex.sum_eq_one,mul_one]
    ring
  have hc : Continuous h := by
    apply continuous_pi
    intro j
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      ((continuous_apply j).comp (a.continuous.subtype_val.comp continuous_snd))).add
      (continuous_fst.subtype_val.mul
        ((continuous_apply j).comp (b.continuous.subtype_val.comp continuous_snd)))
  refine ⟨{
    toFun := fun z => ⟨h z,hn z,hs z⟩
    continuous_toFun := hc.subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ },fun _ _ _ => rfl⟩
  · intro x
    apply stdSimplex.ext
    funext j
    change (1 - (0 : ℝ)) * a x j + (0 : ℝ) * b x j = (a x).val j
    simp only [sub_zero,one_mul,zero_mul,add_zero]
    rfl
  · intro x
    apply stdSimplex.ext
    funext j
    change (1 - (1 : ℝ)) * a x j + (1 : ℝ) * b x j = (b x).val j
    simp only [sub_self,zero_mul,one_mul,zero_add]
    rfl

end KIP126.Topology.Simplex
