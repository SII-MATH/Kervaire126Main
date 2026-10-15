module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

/-- A single-slot monomial of integer degree `n`, now including the
constant monomial. Negative degrees are not truncated to zero. -/
abbrev MilnorMonomial (n : ℤ) := {d : ℕ →₀ ℕ // (slotWeight d : ℤ) = n}

/-- The constant monomial, present in degree zero only. -/
def zeroMilnorMonomial : MilnorMonomial 0 := ⟨0, by simp [slotWeight]⟩

end KIP126.Steenrod.Milnor
