module

public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace KIP126.Steenrod.Milnor

open scoped BigOperators

/-- Eight binary Lucas digits suffice for the coefficients of degree 128.
This is a small computable natural number, not an external certificate. -/
def binaryChooseParity (n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range 8, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2

end KIP126.Steenrod.Milnor
