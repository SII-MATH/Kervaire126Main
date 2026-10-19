module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

public import KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Intervals

@[expose] section

/-! Square-zero for the specified polynomial cobar differential.

The proof uses the Milnor coproduct formula directly: its iterated coproducts
agree by a finite-sum reindexing and Frobenius in characteristic two. Splitting
separate slots commutes, and the resulting double sum cancels by an explicit
fixed-point-free involution. No Adams tower or page comparison is used. -/

namespace KIP126.AdamsSynthetic.Milnor

noncomputable section

open MvPolynomial
open scoped BigOperators

private theorem milnorSum_assoc {R : Type*} [CommSemiring R] [CharP R 2]
    (A B C : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range (n - i + 1), A (n - i - k) ^ (2 ^ k) * B k) ^ (2 ^ i) * C i) =
    ∑ i ∈ Finset.range (n + 1), A (n - i) ^ (2 ^ i) *
      (∑ k ∈ Finset.range (i + 1), B (i - k) ^ (2 ^ k) * C k) := by
  simp only [sum_pow_char_pow, mul_pow, ← pow_mul, ← pow_add, Finset.sum_mul,
    Finset.mul_sum]
  let f : ℕ → ℕ → R := fun i k =>
    A (n - (i + k)) ^ (2 ^ (i + k)) * B k ^ (2 ^ i) * C i
  calc
    _ = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1 - i), f i k := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hr : n - i + 1 = n + 1 - i := by omega
      rw [hr]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [f, Nat.sub_sub, Nat.add_comm k i]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (i + 1), f k (i - k) :=
      (Finset.sum_range_diag_flip (n + 1) f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ i := by have := Finset.mem_range.mp hk; omega
      simp only [f, Nat.add_sub_of_le hk', mul_assoc]

private theorem splitSlot_xi_self {s : ℕ} (slot : Fin s) (n : ℕ) :
    splitSlot slot (xi slot n) =
      ∑ i ∈ Finset.range (n + 1),
        xi slot.castSucc (n - i) ^ (2 ^ i) * xi slot.succ i := by
  cases n <;> simp [xi, splitSlot, coproductGenerator]

private theorem splitSlot_xi_other {s : ℕ} (slot other : Fin s) (h : other ≠ slot)
    (n : ℕ) :
    splitSlot slot (xi other n) =
      xi (if other < slot then other.castSucc else other.succ) n := by
  cases n <;> simp [xi, splitSlot, h]

private theorem coproductGenerator_coassoc {s : ℕ} (slot : Fin s) (j : ℕ) :
    splitSlot slot.castSucc (coproductGenerator slot j) =
      splitSlot slot.succ (coproductGenerator slot j) := by
  have hne : slot.succ ≠ slot.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have hlt : slot.castSucc < slot.succ := by
    change slot.val < slot.val + 1
    omega
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    splitSlot_xi_self, splitSlot_xi_other _ _ hne,
    splitSlot_xi_other _ _ hne.symm, if_pos hlt,
    if_neg (not_lt_of_ge hlt.le)]
  have heq : slot.succ.castSucc = slot.castSucc.succ := Fin.ext rfl
  simp only [heq]
  exact milnorSum_assoc
    (xi slot.castSucc.castSucc) (xi slot.castSucc.succ) (xi slot.succ.succ) (j + 1)

private theorem splitSlot_coproduct_before {s : ℕ} (i j : Fin s) (h : i < j) (n : ℕ) :
    splitSlot i.castSucc (coproductGenerator j n) = coproductGenerator j.succ n := by
  have h₁ : j.castSucc ≠ i.castSucc := fun he => (ne_of_gt h) (Fin.castSucc_injective _ he)
  have h₂ : j.succ ≠ i.castSucc := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    have hij : i.val < j.val := h
    omega
  have hlt₁ : ¬ j.castSucc < i.castSucc := by simpa using not_lt_of_gt h
  have hlt₂ : ¬ j.succ < i.castSucc := by
    change ¬ j.val + 1 < i.val
    have hij : i.val < j.val := h
    omega
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    splitSlot_xi_other _ _ h₁, splitSlot_xi_other _ _ h₂,
    if_neg hlt₁, if_neg hlt₂]
  have he : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
  simp only [he]

private theorem splitSlot_coproduct_after {s : ℕ} (i j : Fin s) (h : i < j) (n : ℕ) :
    splitSlot j.succ (coproductGenerator i n) = coproductGenerator i.castSucc n := by
  have h₁ : i.castSucc ≠ j.succ := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    have hij : i.val < j.val := h
    omega
  have h₂ : i.succ ≠ j.succ := fun he => (ne_of_lt h) (Fin.succ_injective _ he)
  have hlt₁ : i.castSucc < j.succ := by
    change i.val < j.val + 1
    have hij : i.val < j.val := h
    omega
  have hlt₂ : i.succ < j.succ := by simpa using h
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    splitSlot_xi_other _ _ h₁, splitSlot_xi_other _ _ h₂,
    if_pos hlt₁, if_pos hlt₂]
  have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simp only [he]

private theorem splitSlot_X {s : ℕ} (slot : Fin s) (a : Fin s × ℕ) :
    splitSlot slot (X a) = if a.1 = slot then coproductGenerator slot a.2
      else X (if a.1 < slot then a.1.castSucc else a.1.succ, a.2) := by
  simp only [splitSlot, aeval_X]

private theorem splitSlot_comm {s : ℕ} (i j : Fin s) (h : i ≤ j) (x : TensorPower s) :
    splitSlot j.succ (splitSlot i x) = splitSlot i.castSucc (splitSlot j x) := by
  have he : (splitSlot j.succ).comp (splitSlot i) =
      (splitSlot i.castSucc).comp (splitSlot j) := by
    ext a : 1
    simp only [AlgHom.comp_apply, splitSlot_X]
    by_cases ha : a.1 = i
    · subst i
      simp only
      by_cases hij : a.1 = j
      · subst j
        simpa only [if_true, if_pos rfl] using (coproductGenerator_coassoc a.1 a.2).symm
      · have hij' : a.1 < j := lt_of_le_of_ne h hij
        simp only [if_neg hij, if_pos hij', splitSlot_X]
        exact splitSlot_coproduct_after a.1 j hij' a.2
    · simp only [if_neg ha]
      by_cases haj : a.1 = j
      · subst j
        have hij : i < a.1 := lt_of_le_of_ne h (Ne.symm ha)
        have hn : ¬ a.1 < i := not_lt_of_ge h
        simp only [if_neg hn, splitSlot_X]
        exact (splitSlot_coproduct_before i a.1 hij a.2).symm
      · simp only [if_neg haj]
        have haVal : a.1.val ≠ i.val := fun he => ha (Fin.ext he)
        have hajVal : a.1.val ≠ j.val := fun he => haj (Fin.ext he)
        have hijVal : i.val ≤ j.val := h
        split_ifs <;> simp only [splitSlot_X]
        all_goals split_ifs
        all_goals first
          | solve | exfalso
                    simp only [Fin.ext_iff, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
                    omega
          | apply congrArg X
            apply Prod.ext
            · apply Fin.ext
              simp only [Fin.val_succ, Fin.val_castSucc]
            · rfl
  exact DFunLike.congr_fun he x

private theorem splitSlot_zero_insertLeft (s : ℕ) (x : TensorPower s) :
    splitSlot (0 : Fin (s + 1)) (insertLeft s x) =
      insertLeft (s + 1) (insertLeft s x) := by
  have he : (splitSlot (0 : Fin (s + 1))).comp (insertLeft s) =
      (insertLeft (s + 1)).comp (insertLeft s) := by
    ext a : 1
    simp [splitSlot, insertLeft]
  exact DFunLike.congr_fun he x

private theorem splitSlot_last_insertRight (s : ℕ) (x : TensorPower s) :
    splitSlot (Fin.last s) (insertRight s x) =
      insertRight (s + 1) (insertRight s x) := by
  have he : (splitSlot (Fin.last s)).comp (insertRight s) =
      (insertRight (s + 1)).comp (insertRight s) := by
    ext a : 1
    simp [splitSlot, insertRight]
  exact DFunLike.congr_fun he x

private theorem splitSlot_succ_insertLeft {s : ℕ} (i : Fin s) (x : TensorPower s) :
    splitSlot i.succ (insertLeft s x) = insertLeft (s + 1) (splitSlot i x) := by
  apply splitSlot_rename Fin.succ Fin.succ i i.succ
  · intro a
    exact Fin.succ_inj
  · exact Fin.ext rfl
  · rfl
  · intro a ha
    split_ifs with h h'
    all_goals first
      | exact Fin.ext rfl
      | exfalso
        simp only [Fin.lt_def, Fin.val_succ] at *
        omega

private theorem splitSlot_castSucc_insertRight {s : ℕ} (i : Fin s) (x : TensorPower s) :
    splitSlot i.castSucc (insertRight s x) = insertRight (s + 1) (splitSlot i x) := by
  apply splitSlot_rename Fin.castSucc Fin.castSucc i i.castSucc
  · intro a
    exact Fin.castSucc_inj
  · rfl
  · exact Fin.ext rfl
  · intro a ha
    split_ifs with h h'
    all_goals first
      | exact Fin.ext rfl
      | exfalso
        simp only [Fin.lt_def, Fin.val_castSucc] at *
        omega

private theorem insertLeft_insertRight (s : ℕ) (x : TensorPower s) :
    insertLeft (s + 1) (insertRight s x) = insertRight (s + 1) (insertLeft s x) := by
  have he : (insertLeft (s + 1)).comp (insertRight s) =
      (insertRight (s + 1)).comp (insertLeft s) := by
    ext a : 1
    simp only [AlgHom.comp_apply, insertLeft, insertRight, rename_X]
    rfl
  exact DFunLike.congr_fun he x

private theorem differentialPolynomial_squared_of_split_sum (s : ℕ) (x : TensorPower s)
    (hsplit : (∑ j : Fin (s + 1), ∑ i : Fin s, splitSlot j (splitSlot i x)) = 0) :
    differentialPolynomial (s + 1) (differentialPolynomial s x) = 0 := by
  classical
  have hleft : (∑ j : Fin (s + 1), splitSlot j (insertLeft s x)) =
      insertLeft (s + 1) (insertLeft s x) + ∑ i : Fin s, insertLeft (s + 1) (splitSlot i x) := by
    rw [Fin.sum_univ_succ]
    simp only [splitSlot_zero_insertLeft, splitSlot_succ_insertLeft]
  have hright : (∑ j : Fin (s + 1), splitSlot j (insertRight s x)) =
      (∑ i : Fin s, insertRight (s + 1) (splitSlot i x)) +
        insertRight (s + 1) (insertRight s x) := by
    rw [Fin.sum_univ_castSucc]
    simp only [splitSlot_last_insertRight, splitSlot_castSucc_insertRight]
  simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, map_add, map_sum, Finset.sum_add_distrib]
  have hsplit' : (∑ i : Fin s, ∑ j : Fin (s + 1), splitSlot j (splitSlot i x)) = 0 := by
    rw [Finset.sum_comm]
    exact hsplit
  rw [hleft, hright, hsplit', insertLeft_insertRight]
  abel_nf
  simp only [two_zsmul, CharTwo.add_self_eq_zero]


private def slotPairSwap (s : ℕ) (a : Fin (s + 1) × Fin s) : Fin (s + 1) × Fin s :=
  if h : a.1.val ≤ a.2.val then
    (a.2.succ, ⟨a.1.val, lt_of_le_of_lt h a.2.isLt⟩)
  else
    (a.2.castSucc, ⟨a.1.val - 1, by have := a.1.isLt; omega⟩)

private theorem slotPairSwap_ne (s : ℕ) (a : Fin (s + 1) × Fin s) :
    slotPairSwap s a ≠ a := by
  intro he
  have h₁ := congrArg (fun p => (p.1 : Fin (s + 1)).val) he
  have h₂ := congrArg (fun p => (p.2 : Fin s).val) he
  unfold slotPairSwap at h₁ h₂
  split_ifs at h₁ h₂ with h <;> simp only [Fin.val_succ, Fin.val_castSucc] at * <;> omega

private theorem slotPairSwap_involutive (s : ℕ) (a : Fin (s + 1) × Fin s) :
    slotPairSwap s (slotPairSwap s a) = a := by
  unfold slotPairSwap
  split_ifs with h h' h'
  all_goals first
    | solve | exfalso; simp only [Fin.val_succ, Fin.val_castSucc] at *; omega
    | apply Prod.ext
      · apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc] at * <;> omega
      · apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc] at * <;> omega

private theorem sum_slot_comm_zero {M : Type*} [AddCommMonoid M]
    (zero_two : ∀ x : M, x + x = 0) (s : ℕ)
    (f : Fin (s + 1) → Fin s → M)
    (hcomm : ∀ i j : Fin s, i ≤ j → f j.succ i = f i.castSucc j) :
    ∑ j : Fin (s + 1), ∑ i : Fin s, f j i = 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun a : Fin (s + 1) × Fin s => f a.1 a.2)]
  apply Finset.sum_ninvolution (slotPairSwap s)
  · intro a
    suffices he : f a.1 a.2 = f (slotPairSwap s a).1 (slotPairSwap s a).2 by
      rw [← he]
      exact zero_two _
    unfold slotPairSwap
    split_ifs with h
    · let i : Fin s := ⟨a.1.val, lt_of_le_of_lt h a.2.isLt⟩
      have he : a.1 = i.castSucc := Fin.ext rfl
      have hi : i ≤ a.2 := h
      simpa only [he, Fin.val_castSucc] using (hcomm i a.2 hi).symm
    · let j : Fin s := ⟨a.1.val - 1, by have := a.1.isLt; omega⟩
      have he : a.1 = j.succ := Fin.ext (by dsimp [j]; omega)
      have hj : a.2 ≤ j := by change a.2.val ≤ a.1.val - 1; omega
      simpa only [he, Fin.val_succ, Nat.add_sub_cancel] using hcomm a.2 j hj
  · intro a ha
    exact slotPairSwap_ne s a
  · intro a
    exact Finset.mem_univ _
  · intro a
    exact slotPairSwap_involutive s a

private theorem differentialPolynomial_squared (s : ℕ) (x : TensorPower s) :
    differentialPolynomial (s + 1) (differentialPolynomial s x) = 0 := by
  apply differentialPolynomial_squared_of_split_sum
  exact sum_slot_comm_zero CharTwo.add_self_eq_zero s
    (fun j i => splitSlot j (splitSlot i x)) (fun i j h => splitSlot_comm i j h x)

/-- The fixed Milnor cobar differential squares to zero, by the coproduct formula. -/
public theorem differential_squared (s t : ℕ) (x : cochains s t) :
    differential (s + 1) t (differential s t x) = 0 := by
  apply Subtype.ext
  change differentialPolynomial (s + 1) (differentialPolynomial s x.val) = 0
  exact differentialPolynomial_squared s x.val

end

end KIP126.AdamsSynthetic.Milnor
