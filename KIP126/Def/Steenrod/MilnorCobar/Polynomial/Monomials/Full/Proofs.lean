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

end KIP126.Steenrod.Milnor
