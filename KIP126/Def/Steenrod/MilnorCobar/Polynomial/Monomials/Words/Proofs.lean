module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Basis.Proofs

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open scoped BigOperators

theorem slotExponentsEquiv_apply (s : ℕ) (d : (Fin s × ℕ) →₀ ℕ)
    (i : Fin s) (j : ℕ) : slotExponentsEquiv s d i j = d (i, j) := rfl

theorem usesSlot_iff_exponents_ne_zero {s : ℕ} (d : (Fin s × ℕ) →₀ ℕ)
    (i : Fin s) : UsesSlot d i ↔ slotExponentsEquiv s d i ≠ 0 := by
  simp only [UsesSlot, ne_eq, Finsupp.ext_iff, Finsupp.zero_apply,
    slotExponentsEquiv_apply, not_forall]

/-- The polynomial weight is the sum of the individual slot weights. -/
theorem weight_eq_sum_slotWeight {s : ℕ} (d : (Fin s × ℕ) →₀ ℕ) :
    Finsupp.weight weight d = ∑ i, slotWeight (slotExponentsEquiv s d i) := by
  classical
  change d.sum (fun a n => n • weight a) = _
  rw [← Finsupp.sum_curry_index d (fun i j n => n • weight (i, j))]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  rfl

theorem wordDegree_slotExponents {s : ℕ} (d : (Fin s × ℕ) →₀ ℕ) :
    wordDegree (slotExponentsEquiv s d) = (Finsupp.weight weight d : ℤ) := by
  rw [weight_eq_sum_slotWeight, Nat.cast_sum]
  rfl

theorem wordDegree_cons {s : ℕ} (a : ℕ →₀ ℕ) (d : Fin s → ℕ →₀ ℕ) :
    wordDegree (Fin.cons a d) = (slotWeight a : ℤ) + wordDegree d := by
  simp [wordDegree, Fin.sum_univ_succ]

theorem milnorWord_degree_nonneg {s : ℕ} {t : ℤ} (d : MilnorWord s t) : 0 ≤ t := by
  rw [← d.property.1]
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem milnorWord_zero_degree {t : ℤ} (d : MilnorWord 0 t) : t = 0 := by
  simpa [wordDegree] using d.property.1.symm

end

end KIP126.Steenrod.Milnor
