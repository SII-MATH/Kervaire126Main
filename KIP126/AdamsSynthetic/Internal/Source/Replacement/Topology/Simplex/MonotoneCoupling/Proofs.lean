module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Preorder.Chain

@[expose] section

namespace KIP126.Topology.Simplex

open Finset

/-- Cumulative barycentric mass starts at zero. -/
@[simp] theorem cumulative_zero {n : ℕ} (x : stdSimplex ℝ (Fin (n+1))) :
    cumulative x 0 = 0 := by simp [cumulative]

/-- The final cut contains exactly the total barycentric mass. -/
@[simp] theorem cumulative_total {n : ℕ} (x : stdSimplex ℝ (Fin (n+1))) :
    cumulative x (n+1) = 1 := by
  simp only [cumulative,Fin.is_lt,ite_true]
  exact stdSimplex.sum_eq_one x

/-- Cumulative masses increase with the cut. -/
theorem cumulative_monotone {n : ℕ} (x : stdSimplex ℝ (Fin (n+1))) :
    Monotone (cumulative x) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k hk
  split_ifs with hki hkj
  · rfl
  · exact (hkj (lt_of_lt_of_le hki hij)).elim
  · exact stdSimplex.zero_le x k
  · rfl

/-- Every partial cumulative mass is between zero and one. -/
theorem cumulative_bounds {n : ℕ} (x : stdSimplex ℝ (Fin (n+1)))
    {k : ℕ} (hk : k ≤ n+1) : 0 ≤ cumulative x k ∧ cumulative x k ≤ 1 := by
  constructor
  · simpa only [cumulative_zero] using cumulative_monotone x (Nat.zero_le k)
  · simpa only [cumulative_total] using cumulative_monotone x hk

/-- Consecutive cuts differ by precisely one barycentric coordinate. -/
theorem cumulative_succ {n : ℕ} (x : stdSimplex ℝ (Fin (n+1))) (k : Fin (n+1)) :
    cumulative x (k.1+1) = cumulative x k.1 + x k := by
  classical
  have hfun (i : Fin (n+1)) :
      (if i.1 < k.1+1 then x i else 0) =
        (if i.1 < k.1 then x i else 0) + (if i = k then x k else 0) := by
    by_cases hi : i = k
    · subst i
      simp
    · have hne : i.1 ≠ k.1 := fun h => hi (Fin.ext h)
      by_cases hik : i.1 < k.1
      · simp [hi,hik,Nat.lt_succ_of_lt hik]
      · have hge : ¬ i.1 < k.1+1 := by omega
        simp [hi,hik,hge]
  simp only [cumulative,hfun,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- A finite successive-difference sum telescopes, including dimension zero. -/
theorem sum_fin_successive_difference {n : ℕ} (f : Fin (n+1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  have h₀ := Fin.sum_univ_succ f
  have h₁ := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

/-- The mixed minimum difference is the length of intersection of two
ordered intervals. -/
theorem mixed_min_eq_intersection {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    min b d - min a d - min b c + min a c = max 0 (min b d - max a c) := by
  rcases le_total b c with hbc | hcb
  · rw [min_eq_left (hbc.trans hcd),min_eq_left (hab.trans (hbc.trans hcd)),
      min_eq_left hbc,min_eq_left (hab.trans hbc),max_eq_right (hab.trans hbc),
      max_eq_left (sub_nonpos.mpr hbc)]
    ring
  · rcases le_total d a with hda | had
    · rw [min_eq_right (hda.trans hab),min_eq_right hda,
        min_eq_right (hcd.trans (hda.trans hab)),min_eq_right (hcd.trans hda),
        max_eq_left (hcd.trans hda),max_eq_left (sub_nonpos.mpr hda)]
      ring
    · have h₁ : a ≤ min b d := le_min hab had
      have h₂ : c ≤ min b d := le_min hcb hcd
      rw [min_eq_left had,min_eq_right hcb,max_eq_right (sub_nonneg.mpr (max_le h₁ h₂))]
      have h := min_add_max a c
      linarith

/-- The actual coupling masses are nonnegative. -/
theorem couplingMass_nonneg {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    (i : Fin (p+1)) (j : Fin (q+1)) : 0 ≤ couplingMass x y i j := by
  rw [couplingMass,mixed_min_eq_intersection
    (cumulative_monotone x (Nat.le_succ _)) (cumulative_monotone y (Nat.le_succ _))]
  exact le_max_left _ _

/-- Each row has exactly the prescribed first marginal mass. -/
theorem sum_couplingMass_row {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    (i : Fin (p+1)) : ∑ j, couplingMass x y i j = x i := by
  let f : Fin (q+2) → ℝ := fun j =>
    min (cumulative x (i.1+1)) (cumulative y j.1) -
      min (cumulative x i.1) (cumulative y j.1)
  have he : ∀ j : Fin (q+1), couplingMass x y i j = f j.succ - f j.castSucc := by
    intro j
    dsimp [couplingMass,f]
    ring
  simp_rw [he]
  rw [sum_fin_successive_difference]
  have hi := cumulative_bounds x (Nat.le_of_lt i.2)
  have hi' := cumulative_bounds x (Nat.succ_le_of_lt i.2)
  dsimp [f]
  rw [cumulative_total,cumulative_zero,min_eq_left hi'.2,min_eq_left hi.2,
    min_eq_right hi'.1,min_eq_right hi.1,cumulative_succ]
  ring

/-- Exchanging the marginals exchanges the coupling matrix indices. -/
theorem couplingMass_swap {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    (i : Fin (p+1)) (j : Fin (q+1)) : couplingMass x y i j = couplingMass y x j i := by
  dsimp [couplingMass]
  simp only [min_comm]
  ring

/-- Each column has exactly the prescribed second marginal mass. -/
theorem sum_couplingMass_column {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    (j : Fin (q+1)) : ∑ i, couplingMass x y i j = y j := by
  simp_rw [couplingMass_swap x y]
  exact sum_couplingMass_row y x j

/-- Positive overlap forces each lower cut to precede the other upper cut. -/
theorem couplingMass_pos_cuts {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    {i : Fin (p+1)} {j : Fin (q+1)} (h : 0 < couplingMass x y i j) :
    cumulative x i.1 < cumulative y (j.1+1) ∧
      cumulative y j.1 < cumulative x (i.1+1) := by
  rw [couplingMass,mixed_min_eq_intersection
    (cumulative_monotone x (Nat.le_succ _)) (cumulative_monotone y (Nat.le_succ _))] at h
  have hlt : max (cumulative x i.1) (cumulative y j.1) <
      min (cumulative x (i.1+1)) (cumulative y (j.1+1)) := by
    have hs : 0 < min (cumulative x (i.1+1)) (cumulative y (j.1+1)) -
        max (cumulative x i.1) (cumulative y j.1) := (lt_max_iff.mp h).resolve_left (lt_irrefl 0)
    exact sub_pos.mp hs
  exact ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlt (min_le_right _ _)),
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlt (min_le_left _ _))⟩

/-- Positive entries of the coupling cannot cross in the product order. -/
theorem couplingMass_no_crossing {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    {i i' : Fin (p+1)} {j j' : Fin (q+1)} (hi : i < i') (hj : j' < j)
    (h : 0 < couplingMass x y i j) (h' : 0 < couplingMass x y i' j') : False := by
  have hc := (couplingMass_pos_cuts x y h).2
  have hc' := (couplingMass_pos_cuts x y h').1
  have hx := cumulative_monotone x (Nat.succ_le_of_lt hi)
  have hy := cumulative_monotone y (Nat.succ_le_of_lt hj)
  linarith

/-- The support of the actual coupling is a chain of product vertices. -/
theorem couplingMass_support_isChain {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1))) :
    IsChain (· ≤ ·) {a : Fin (p+1) × Fin (q+1) | 0 < couplingMass x y a.1 a.2} := by
  intro a ha b hb hab
  rcases lt_trichotomy a.1 b.1 with hi | hi | hi
  · left
    refine ⟨hi.le,?_⟩
    by_contra hj
    exact couplingMass_no_crossing x y hi (lt_of_not_ge hj) ha hb
  · rcases le_total a.2 b.2 with hj | hj
    · exact Or.inl ⟨hi.le,hj⟩
    · exact Or.inr ⟨hi.ge,hj⟩
  · right
    refine ⟨hi.le,?_⟩
    by_contra hj
    exact couplingMass_no_crossing x y hi (lt_of_not_ge hj) hb ha

/-- Two barycentric distributions admit an actual chain-supported joint
distribution with exactly those two marginals. -/
theorem exists_chain_coupling {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1))) :
    ∃ w : stdSimplex ℝ (Fin (p+1) × Fin (q+1)),
      stdSimplex.map Prod.fst w = x ∧ stdSimplex.map Prod.snd w = y ∧
      IsChain (· ≤ ·) {a | 0 < w a} := by
  classical
  let w : stdSimplex ℝ (Fin (p+1) × Fin (q+1)) :=
    ⟨fun a => couplingMass x y a.1 a.2,
      fun a => couplingMass_nonneg x y a.1 a.2,by
        rw [Fintype.sum_prod_type]
        simp only [sum_couplingMass_row]
        exact stdSimplex.sum_eq_one x⟩
  refine ⟨w,?_,?_,couplingMass_support_isChain x y⟩
  · apply stdSimplex.ext
    funext i
    change FunOnFinite.linearMap ℝ ℝ Prod.fst w i = x i
    rw [FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Fintype.sum_prod_type]
    simp only [w,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact sum_couplingMass_row x y i
  · apply stdSimplex.ext
    funext j
    change FunOnFinite.linearMap ℝ ℝ Prod.snd w j = y j
    rw [FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Fintype.sum_prod_type]
    simp only [w,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact sum_couplingMass_column x y j

end KIP126.Topology.Simplex
