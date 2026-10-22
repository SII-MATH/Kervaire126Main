module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Proofs

@[expose] section

namespace KIP126.Topology.Simplex

open Finset

/-- If positive masses cannot occur on both opposing sides of two cuts,
their common mass is the minimum of the two marginal cut masses. -/
theorem sum_intersection_eq_min_of_no_crossing {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (P Q : A → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hcross : ∀ a b, P a → ¬ Q a → Q b → ¬ P b → 0 < w a → 0 < w b → False) :
    (∑ a, if P a ∧ Q a then w a else 0) =
      min (∑ a, if P a then w a else 0) (∑ a, if Q a then w a else 0) := by
  classical
  have hleP : (∑ a, if P a ∧ Q a then w a else 0) ≤ ∑ a, if P a then w a else 0 := by
    apply Finset.sum_le_sum
    intro a _
    split_ifs <;> aesop
  have hleQ : (∑ a, if P a ∧ Q a then w a else 0) ≤ ∑ a, if Q a then w a else 0 := by
    apply Finset.sum_le_sum
    intro a _
    split_ifs <;> aesop
  by_cases h : ∀ a, P a → ¬ Q a → w a = 0
  · have he : (∑ a, if P a ∧ Q a then w a else 0) = ∑ a, if P a then w a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,h a]
    rw [he,min_eq_left (he ▸ hleQ)]
  · push Not at h
    obtain ⟨a,hpa,hqa,hwa⟩ := h
    have he : (∑ b, if P b ∧ Q b then w b else 0) = ∑ b, if Q b then w b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hp : P b <;> by_cases hq : Q b
      · simp [hp,hq]
      · simp [hp,hq]
      · have hwb : w b = 0 := by
          by_contra hwb
          exact hcross a b hpa hqa hq hp (lt_of_le_of_ne (hw a) (Ne.symm hwa))
            (lt_of_le_of_ne (hw b) (Ne.symm hwb))
        simp [hp,hq,hwb]
      · simp [hp,hq]
    rw [he,min_eq_right (he ▸ hleP)]

/-- The joint cumulative mass of a chain-supported distribution is the
minimum of its two marginal cumulative masses. -/
theorem chain_coupling_cumulative {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1)))
    (hw : IsChain (· ≤ ·) {a | 0 < w a}) (r s : ℕ) :
    (∑ a, if a.1.val < r ∧ a.2.val < s then w a else 0) =
      min (∑ a, if a.1.val < r then w a else 0)
        (∑ a, if a.2.val < s then w a else 0) := by
  apply sum_intersection_eq_min_of_no_crossing w (stdSimplex.zero_le w)
  intro a b ha hna hb hnb hwa hwb
  have hab : a ≠ b := by intro h; subst b; exact hnb ha
  rcases hw hwa hwb hab with hab | hba
  · have h₂ := hab.2
    change a.2.val ≤ b.2.val at h₂
    omega
  · have h₁ := hba.1
    change b.1.val ≤ a.1.val at h₁
    omega

/-- Four consecutive joint cumulative masses recover one matrix entry. -/
theorem joint_cumulative_difference {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1)))
    (i : Fin (p+1)) (j : Fin (q+1)) :
    (∑ a, if a.1.val < i.val+1 ∧ a.2.val < j.val+1 then w a else 0) -
      (∑ a, if a.1.val < i.val ∧ a.2.val < j.val+1 then w a else 0) -
      (∑ a, if a.1.val < i.val+1 ∧ a.2.val < j.val then w a else 0) +
      (∑ a, if a.1.val < i.val ∧ a.2.val < j.val then w a else 0) = w (i,j) := by
  classical
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  calc
    _ = ∑ a, if a = (i,j) then w (i,j) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hi : a.1 = i
      · by_cases hj : a.2 = j
        · have h : a = (i,j) := Prod.ext hi hj
          subst a
          simp
        · have hne : a.2.val ≠ j.val := fun h => hj (Fin.ext h)
          have he : a.2.val < j.val+1 ↔ a.2.val < j.val := by omega
          have ha : a ≠ (i,j) := fun h => hj (congrArg Prod.snd h)
          simp only [he,if_neg ha]
          ring
      · have hne : a.1.val ≠ i.val := fun h => hi (Fin.ext h)
        have he : a.1.val < i.val+1 ↔ a.1.val < i.val := by omega
        have ha : a ≠ (i,j) := fun h => hi (congrArg Prod.fst h)
        simp only [he,if_neg ha]
        ring
    _ = _ := by simp

/-- The first marginal of a joint simplex is its row sum. -/
theorem marginal_fst_apply {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1))) (i : Fin (p+1)) :
    stdSimplex.map Prod.fst w i = ∑ j, w (i,j) := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Prod.fst w i = _
  rw [FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  simp

/-- The second marginal of a joint simplex is its column sum. -/
theorem marginal_snd_apply {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1))) (j : Fin (q+1)) :
    stdSimplex.map Prod.snd w j = ∑ i, w (i,j) := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Prod.snd w j = _
  rw [FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem cumulative_marginal_fst {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1))) (r : ℕ) :
    (∑ a, if a.1.val < r then w a else 0) = cumulative (stdSimplex.map Prod.fst w) r := by
  rw [cumulative,Fintype.sum_prod_type]
  simp only [marginal_fst_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r <;> simp [hi]

theorem cumulative_marginal_snd {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1))) (s : ℕ) :
    (∑ a, if a.2.val < s then w a else 0) = cumulative (stdSimplex.map Prod.snd w) s := by
  rw [cumulative,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [marginal_snd_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < s <;> simp [hj]

/-- Every chain-supported joint distribution is the displayed canonical
mixed-minimum coupling of its two marginals. -/
theorem chain_coupling_eq_couplingMass {p q : ℕ}
    (w : stdSimplex ℝ (Fin (p+1) × Fin (q+1)))
    (hw : IsChain (· ≤ ·) {a | 0 < w a}) (i : Fin (p+1)) (j : Fin (q+1)) :
    w (i,j) = couplingMass (stdSimplex.map Prod.fst w) (stdSimplex.map Prod.snd w) i j := by
  have h := joint_cumulative_difference w i j
  simp_rw [chain_coupling_cumulative w hw,cumulative_marginal_fst,cumulative_marginal_snd] at h
  exact h.symm

/-- Two chain-supported joint barycentric distributions with the same
two marginals are equal. -/
theorem chain_coupling_unique {p q : ℕ}
    (w w' : stdSimplex ℝ (Fin (p+1) × Fin (q+1)))
    (hw : IsChain (· ≤ ·) {a | 0 < w a})
    (hw' : IsChain (· ≤ ·) {a | 0 < w' a})
    (hfst : stdSimplex.map Prod.fst w = stdSimplex.map Prod.fst w')
    (hsnd : stdSimplex.map Prod.snd w = stdSimplex.map Prod.snd w') : w = w' := by
  apply stdSimplex.ext
  funext a
  obtain ⟨i,j⟩ := a
  rw [chain_coupling_eq_couplingMass w hw,chain_coupling_eq_couplingMass w' hw',hfst,hsnd]

end KIP126.Topology.Simplex
