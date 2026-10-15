module

public import KIP126.Def.Synthetic.QuotientMap.Data

@[expose] public section

/-!
The finite λ-Bockstein arrow is a composite of the actual λ-power cofiber
boundary and the shifted first-quotient inclusion. This construction requires
neither a separately chosen quotient tower nor a spectral-sequence comparison.
-/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The actual finite Bockstein arrow. Intrinsic exponent `q` corresponds
to page `q + 1` in the later synthetic Adams comparison; no such comparison
is part of this definition. -/
noncomputable def beta (A : Syn) (q : ℕ) :
    XModLambdaN A q ⟶
      ((SyntheticCategory.biShift (0, -(q : ℤ))).obj (XModLambdaN A 1))⟦(1 : ℤ)⟧ :=
  XModLambdaN.proj A q ≫ (shiftFunctor Syn (1 : ℤ)).map
    ((SyntheticCategory.biShift (0, -(q : ℤ))).map (XModLambdaN.incl A 1))

end KIP126.Synthetic.Bockstein
