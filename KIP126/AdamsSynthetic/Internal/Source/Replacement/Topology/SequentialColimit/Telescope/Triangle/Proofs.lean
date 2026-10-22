module

import Mathlib.Topology.Homotopy.Basic

@[expose] section

namespace KIP126.Topology.SequentialColimit

open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- The triangle expressing a concatenation has an actual continuous
filling: its bottom is constant, its top is the second path, and its
vertical sides are the first path and the full concatenation. The source
may be arbitrary, so the construction retains all space parameters. -/
theorem exists_homotopy_concat_triangle
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X,Y)} (H : f.Homotopy g) (K : g.Homotopy h) :
    ∃ L : (f.comp ContinuousMap.snd).Homotopy K.toContinuousMap,
      (∀ (t : I) (x : X), L (t,(0,x)) = H (t,x)) ∧
      ∀ (t : I) (x : X), L (t,(1,x)) = (H.trans K) (t,x) := by
  let C := H.trans K
  have left (q t : I) (hq : (q : ℝ) ≤ 1/2) (ht : 2*(q : ℝ) = (t : ℝ)) (x : X) :
      C (q,x) = H (t,x) := by
    rw [ContinuousMap.Homotopy.trans_apply, dif_pos hq]
    congr 1
    exact Prod.ext (Subtype.ext ht) rfl
  have right (q t : I) (hq : 1/2 ≤ (q : ℝ)) (ht : 2*(q : ℝ)-1 = (t : ℝ)) (x : X) :
      C (q,x) = K (t,x) := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with hq'
    · have ht0 : t = 0 := Subtype.ext (by dsimp; linarith)
      rw [ht0,K.apply_zero]
      apply Eq.trans ?_ (H.apply_one x)
      congr 1
      exact Prod.ext (Subtype.ext (by dsimp; linarith)) rfl
    · congr 1
      exact Prod.ext (Subtype.ext ht) rfl
  let p : C(I × I,I) := ⟨fun z => ⟨(z.1 : ℝ)*(1+(z.2 : ℝ))/2,
    ⟨div_nonneg (mul_nonneg z.1.property.1 (by linarith [z.2.property.1])) (by norm_num),by
      have hm := mul_le_mul_of_nonneg_left z.2.property.2 z.1.property.1
      nlinarith [z.1.property.2]⟩⟩,
    (((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))).div_const 2).subtype_mk _⟩
  have pzero (s : I) : p (0,s) = 0 := Subtype.ext (by dsimp [p]; ring)
  have pone (t : I) : p (t,1) = t := Subtype.ext (by dsimp [p]; ring)
  let L : (f.comp ContinuousMap.snd).Homotopy K.toContinuousMap := {
    toContinuousMap := C.toContinuousMap.comp
      ⟨fun z => (p (z.1,z.2.1),z.2.2),
        (p.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd⟩
    map_zero_left := by
      rintro ⟨s,x⟩
      change C (p (0,s),x) = f x
      rw [pzero,C.apply_zero]
    map_one_left := by
      rintro ⟨s,x⟩
      exact right (p (1,s)) s (by dsimp [p]; nlinarith [s.property.1])
        (by dsimp [p]; ring) x }
  refine ⟨L,?_,?_⟩
  · intro t x
    exact left (p (t,0)) t (by dsimp [p]; nlinarith [t.property.2])
      (by dsimp [p]; ring) x
  · intro t x
    change C (p (t,1),x) = C (t,x)
    rw [pone]

end KIP126.Topology.SequentialColimit
