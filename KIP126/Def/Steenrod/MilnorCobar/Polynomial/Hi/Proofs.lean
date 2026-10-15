module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Hi.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Proofs

@[expose] public section

/-! The Frobenius powers of the primitive generator are normalized cocycles. -/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra MvPolynomial

/-- The representative has internal degree `2^i` and vanishing augmentation. -/
theorem hiPolynomial_mem (i : ℕ) : IsCochain (2 ^ i) (hiPolynomial i) := by
  constructor
  · simpa [hiPolynomial, weight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := F2) (@weight 1) (0, 0)).pow (2 ^ i)
  · change hiPolynomial i ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    have hslot : slot = 0 := Subsingleton.elim _ _
    subst slot
    simp [LinearMap.mem_ker, augmentSlot, hiPolynomial]

/-- Frobenius preserves primitiveness in characteristic two. -/
theorem hiPolynomial_differential (i : ℕ) :
    differentialPolynomial 1 (hiPolynomial i) = 0 := by
  have hp (x y : TensorPower 2) :
      (x + y) ^ (2 ^ i) = x ^ (2 ^ i) + y ^ (2 ^ i) :=
    add_pow_char_pow x y 2 i
  simp [differentialPolynomial, hiPolynomial, insertLeft, insertRight,
    splitSlot, coproductGenerator, xi, Finset.sum_range_succ, hp,
    add_assoc, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left]

/-- Concatenating two `hᵢ` representatives gives internal degree `2^(i+1)`. -/
theorem hiSquare_internalDegree (i : ℕ) : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by
  rw [pow_succ]
  omega

end

end KIP126.Steenrod.Milnor
