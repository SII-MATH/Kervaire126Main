module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar

@[expose] section

/-! Concrete normalized Milnor cobar construction.
Adapted from SII-MATH/Kervaire126 (MIT), develop commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
These internal definitions have no chosen Adams page, named Ext class,
or computation data as input. -/

namespace KIP126.AdamsSynthetic.Milnor

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Polynomial/Hi/Data.lean. -/
noncomputable section

/-- The polynomial representative `[ξ₁^(2^i)]` of `hᵢ`, starting with `i = 0`. -/
def hiPolynomial (i : ℕ) : TensorPower 1 :=
  MvPolynomial.X (0, 0) ^ (2 ^ i)

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Polynomial/Hi/Proofs.lean. -/
noncomputable section

open MvPolynomial

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

@[simp] theorem hiPolynomial_six : hiPolynomial 6 = h6Polynomial := rfl

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Hi/Data.lean. -/
noncomputable section

/-- The standard normalized cochain `[ξ₁^(2^i)]` in bidegree `(1, 2^i)`. -/
def hiCochain (i : ℕ) : cochains 1 (2 ^ i) :=
  ⟨hiPolynomial i, hiPolynomial_mem i⟩

/-- The actual concatenation square, reindexed to bidegree `(2, 2^(i+1))`. -/
def hiSquareCochain (i : ℕ) : cochains 2 (2 ^ (i + 1)) :=
  reindex rfl (hiSquare_internalDegree i) (cup (hiCochain i) (hiCochain i))

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Hi/Proofs.lean. -/
noncomputable section

theorem hiCochain_isCycle (i : ℕ) : IsCycle (hiCochain i) := by
  apply Subtype.ext
  exact hiPolynomial_differential i

theorem hiSquareCochain_isCycle (i : ℕ) : IsCycle (hiSquareCochain i) := by
  have transport (t t' : ℕ) (ht : t = t') (x : cochains 2 t) (hx : IsCycle x) :
      IsCycle (reindex rfl ht x) := by
    subst t'
    exact hx
  exact transport _ _ (hiSquare_internalDegree i) _
    (cup_isCycle _ _ (hiCochain_isCycle i) (hiCochain_isCycle i))

@[simp] theorem hiCochain_six : hiCochain 6 = h6Cochain := rfl

@[simp] theorem hiSquareCochain_six : hiSquareCochain 6 = h6SquareCochain := rfl

end

end KIP126.AdamsSynthetic.Milnor
