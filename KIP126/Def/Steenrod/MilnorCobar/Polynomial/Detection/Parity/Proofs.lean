module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Parity.Data
public import Mathlib.Data.Nat.Choose.Lucas

@[expose] public section

namespace KIP126.Steenrod.Milnor

open KIP126.Algebra
open scoped BigOperators

/-- Agreement with binomial parity is proved using Lucas's theorem. -/
theorem binaryChooseParity_eq (n k : ℕ) (hn : n < 256) (hk : k < 256) :
    binaryChooseParity n k = n.choose k % 2 := by
  exact (Choose.choose_modEq_prod_range_choose_nat (p := 2) (a := 8) hn hk).symm

/-- The finite arithmetic identity used by the square detector.
The kernel checks the 43 cases; no native evaluation axiom is used. -/
theorem h6Square_binary_parity :
    ∀ b : Fin 43,
      (∑ i ∈ Finset.range 7,
        if b.val ≤ 2 ^ i then binaryChooseParity (128 - 3 * b.val) (2 ^ i - b.val) else 0) % 2 = 0 := by
  decide +kernel

/-- The seven actual binomial coefficients cancel in characteristic two. -/
theorem h6Square_binomial_parity (b : Fin 43) :
    (∑ i ∈ Finset.range 7,
      if b.val ≤ 2 ^ i then ((128 - 3 * b.val).choose (2 ^ i - b.val) : F2) else 0) = 0 := by
  have h (i : ℕ) (hi : i ∈ Finset.range 7) :
      ((128 - 3 * b.val).choose (2 ^ i - b.val) : F2) =
        (binaryChooseParity (128 - 3 * b.val) (2 ^ i - b.val) : F2) := by
    have hp : 2 ^ i < 128 := by
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (Finset.mem_range.mp hi)
    rw [binaryChooseParity_eq _ _ (by omega) (by omega)]
    simp
  have he : (∑ i ∈ Finset.range 7,
      if b.val ≤ 2 ^ i then ((128 - 3 * b.val).choose (2 ^ i - b.val) : F2) else 0) =
      ((∑ i ∈ Finset.range 7,
        if b.val ≤ 2 ^ i then binaryChooseParity (128 - 3 * b.val) (2 ^ i - b.val) else 0 : ℕ) : F2) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [h i hi]
  rw [he]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero (h6Square_binary_parity b))

end KIP126.Steenrod.Milnor
