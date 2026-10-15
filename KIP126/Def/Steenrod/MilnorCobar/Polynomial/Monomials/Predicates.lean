module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

/-- A tensor monomial uses a slot if some generator in that slot has
nonzero exponent. This is a condition on the monomial, not its coefficient. -/
def UsesSlot {s : ℕ} (d : (Fin s × ℕ) →₀ ℕ) (slot : Fin s) : Prop :=
  ∃ j, d (slot, j) ≠ 0

/-- The exponents indexing the normalized homogeneous monomial basis. -/
def IsCochainMonomial {s : ℕ} (t : ℕ) (d : (Fin s × ℕ) →₀ ℕ) : Prop :=
  Finsupp.weight weight d = t ∧ ∀ slot, UsesSlot d slot

end KIP126.Steenrod.Milnor
