module

public import KIP126.Def.Steenrod.MilnorCobar.Data
public import Mathlib.Algebra.MvPolynomial.Coeff
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Predicates

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

/-- With no higher generator, a one-slot exponent vector has exactly its
ξ₁ and ξ₂ components. -/
theorem singleSlot_exponents_eq_two (d : (Fin 1 × ℕ) →₀ ℕ)
    (hd : ∀ j, 2 ≤ j → d (0, j) = 0) :
    d = Finsupp.single (0, 0) (d (0, 0)) + Finsupp.single (0, 1) (d (0, 1)) := by
  ext ⟨slot, j⟩
  have hs : slot = 0 := Subsingleton.elim _ _
  subst slot
  rcases j with _ | (_ | j)
  · simp
  · simp
  · simp [hd (j + 1 + 1) (by omega)]

theorem singleSlot_two_weight (a b : ℕ) :
    Finsupp.weight (weight (s := 1))
      (Finsupp.single (0, 0) a + Finsupp.single (0, 1) b) = a + 3 * b := by
  simp [Finsupp.weight_single, weight, mul_comm]

end
end KIP126.Steenrod.Milnor
