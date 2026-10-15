module

public import KIP126.Def.Synthetic.QuotientTower.Data

@[expose] public section

namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X : Syn}

/-- Multiplication by λᵏ from the smaller actual quotient into the larger
one. The zero power is the specified grading-unit isomorphism. -/
def FiniteLambdaQuotientTower.lambdaInclusion (T : FiniteLambdaQuotientTower X)
    (k q : ℕ) (hkq : k < q) :
    (SyntheticCategory.biShift (0, -(k : ℤ))).obj (XModLambdaN X (q - k)) ⟶
      XModLambdaN X q := by
  by_cases hk : k = 0
  · subst k
    change (SyntheticCategory.biShift (0, 0)).obj (XModLambdaN X q) ⟶ XModLambdaN X q
    exact SyntheticCategory.biShift_zero.hom.app (XModLambdaN X q)
  · exact (T.triangle (Nat.pos_of_ne_zero hk) hkq).lambdaMap

end
end KIP126.Synthetic.Context
