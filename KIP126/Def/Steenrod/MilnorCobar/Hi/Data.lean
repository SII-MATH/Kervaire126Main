module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Hi.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Reindex.Data

@[expose] public section

/-! Actual normalized cobar representatives of `hᵢ` and their squares. -/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- The standard normalized cochain `[ξ₁^(2^i)]` in bidegree `(1, 2^i)`. -/
def hiCochain (i : ℕ) : cochains 1 (2 ^ i) :=
  ⟨hiPolynomial i, hiPolynomial_mem i⟩

/-- The actual concatenation square, reindexed to bidegree `(2, 2^(i+1))`. -/
def hiSquareCochain (i : ℕ) : cochains 2 (2 ^ (i + 1)) :=
  reindex rfl (hiSquare_internalDegree i) (cup (hiCochain i) (hiCochain i))

end

end KIP126.Steenrod.Milnor
