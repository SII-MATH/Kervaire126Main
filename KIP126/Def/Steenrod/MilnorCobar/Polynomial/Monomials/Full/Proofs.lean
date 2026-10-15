module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

theorem slotWeight_eq_zero_iff (d : ℕ →₀ ℕ) : slotWeight d = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext j
    by_contra hj
    have hle := Finsupp.le_weight_of_ne_zero' (fun j : ℕ => 2 ^ (j + 1) - 1) hj
    have hp := Nat.one_lt_pow (Nat.succ_ne_zero j) (show 1 < 2 by decide)
    change 2 ^ (j + 1) - 1 ≤ slotWeight d at hle
    omega
  · rintro rfl
    simp [slotWeight]

theorem positiveMonomial_degree_pos {n : ℤ} (d : PositiveMonomial n) : 0 < n := by
  have h := (slotWeight_eq_zero_iff d.val).not.mpr d.property.2
  rw [← d.property.1]
  exact_mod_cast Nat.pos_of_ne_zero h

theorem milnorMonomial_zero_eq (d : MilnorMonomial 0) : d = zeroMilnorMonomial := by
  apply Subtype.ext
  apply (slotWeight_eq_zero_iff d.val).mp
  exact_mod_cast d.property

theorem milnorMonomial_ne_zero {n : ℤ} (hn : n ≠ 0) (d : MilnorMonomial n) :
    d.val ≠ 0 := by
  intro h
  apply hn
  simpa [h, slotWeight] using d.property.symm

/-- In a fixed weight range, only finitely many Milnor exponents can occur.
Both their support and their values are bounded by the weight bound. -/
theorem boundedSlotWeight_finite (n : ℕ) :
    Finite {d : ℕ →₀ ℕ // slotWeight d ≤ n} := by
  classical
  have hpos (j : ℕ) : 2 ^ (j + 1) - 1 ≠ 0 := by
    have h := Nat.lt_two_pow_self (n := j + 1)
    omega
  let f : {d : ℕ →₀ ℕ // slotWeight d ≤ n} → (Fin (n+1) → Fin (n+1)) :=
    fun d j => ⟨d.val j.val, Nat.lt_succ_of_le
      ((Finsupp.le_weight (fun j => 2 ^ (j+1)-1) (hpos j) d.val).trans d.property)⟩
  apply Finite.of_injective f
  intro d e h
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  by_cases hj : j < n + 1
  · exact congrArg Fin.val (congrFun h ⟨j, hj⟩)
  · have hz (a : {d : ℕ →₀ ℕ // slotWeight d ≤ n}) : a.val j = 0 := by
      by_contra hne
      have hw := (Finsupp.le_weight_of_ne_zero'
        (fun k : ℕ => 2 ^ (k+1)-1) hne).trans a.property
      have hp := Nat.lt_two_pow_self (n := j+1)
      omega
    rw [hz d, hz e]

/-- Every integer degree of the polynomial dual Steenrod algebra has a
finite monomial basis, including the constant and the empty negative degrees. -/
theorem milnorMonomial_finite (n : ℤ) : Finite (MilnorMonomial n) := by
  let f : MilnorMonomial n → {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat} :=
    fun d => ⟨d.val, by have h := d.property; omega⟩
  letI := boundedSlotWeight_finite n.toNat
  apply Finite.of_injective f
  intro d e h
  exact Subtype.ext (congrArg
    (fun a : {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat} => a.val) h)

end KIP126.Steenrod.Milnor
