module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Data

@[expose] public section

/-! The standard primitive-power representatives for the entire `hᵢ` family. -/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- The polynomial representative `[ξ₁^(2^i)]` of `hᵢ`, starting with `i = 0`. -/
def hiPolynomial (i : ℕ) : TensorPower 1 :=
  MvPolynomial.X (0, 0) ^ (2 ^ i)

end

end KIP126.Steenrod.Milnor
