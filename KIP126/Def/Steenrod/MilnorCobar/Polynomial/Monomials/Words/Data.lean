module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Predicates

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- Separate the exponents into the finitely many tensor slots. -/
def slotExponentsEquiv (s : ℕ) :
    ((Fin s × ℕ) →₀ ℕ) ≃ (Fin s → ℕ →₀ ℕ) :=
  Finsupp.curryEquiv.trans Finsupp.equivFunOnFinite

/-- Internal degree in one polynomial factor. -/
def slotWeight (d : ℕ →₀ ℕ) : ℕ := Finsupp.weight (fun j => 2 ^ (j + 1) - 1) d

/-- Integer grading makes negative degrees genuinely empty, not truncated to zero. -/
def wordDegree {s : ℕ} (d : Fin s → ℕ →₀ ℕ) : ℤ := ∑ i, (slotWeight (d i) : ℤ)

/-- A word of nonconstant Milnor monomials, with its total internal degree. -/
abbrev MilnorWord (s : ℕ) (t : ℤ) :=
  {d : Fin s → ℕ →₀ ℕ // wordDegree d = t ∧ ∀ i, d i ≠ 0}

end

end KIP126.Steenrod.Milnor
