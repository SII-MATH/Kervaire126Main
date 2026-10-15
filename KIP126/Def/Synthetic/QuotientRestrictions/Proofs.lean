module

public import KIP126.Def.Synthetic.QuotientRestrictions.Data

@[expose] public section

/-! The inclusion and boundary squares for the specified quotient
restrictions. No inverse-limit or completeness conclusion is asserted. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The constructed restriction is a map under the original object `X`. -/
theorem XModLambdaN.incl_restriction (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.incl X j ≫ XModLambdaN.restriction coh X i j hij =
      XModLambdaN.incl X i := by
  symm
  simpa only [XModLambdaN.incl, XModLambdaN.restriction, XModLambdaN,
      Category.id_comp] using
    HasFunctorialCofiber.cofibMap_ι (lambdaPow j X) (lambdaPow i X)
      (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
      (by simpa only [lambdaDegree, Category.comp_id] using
        lambdaRestrictionSourceMap_commutes coh i j hij X)

/-- The boundary square uses the shift of the same power-factorization map. -/
theorem XModLambdaN.restriction_proj (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.restriction coh X i j hij ≫ XModLambdaN.proj X i =
      XModLambdaN.proj X j ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaRestrictionSourceMap i j hij X) :=
  HasFunctorialCofiber.cofibMap_δ (lambdaPow j X) (lambdaPow i X)
    (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
    (by simpa only [lambdaDegree, Category.comp_id] using
      lambdaRestrictionSourceMap_commutes coh i j hij X)

end KIP126.Synthetic.Context
