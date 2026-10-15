module

public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import KIP126.Def.Synthetic.QuotientMap.Data

@[expose] public section

/-! Restriction maps between the actual chosen λ-power cofibers. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The chosen cofiber map of the proved λ-power factorization square.
Both its source and target are the existing `XModLambdaN` objects. This
construction alone does not assert identity or composition laws for the
choice of `HasFunctorialCofiber.cofibMap`. -/
noncomputable def XModLambdaN.restriction (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) : XModLambdaN X j ⟶ XModLambdaN X i :=
  HasFunctorialCofiber.cofibMap (lambdaPow j X) (lambdaPow i X)
    (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
    (by simpa only [lambdaDegree, Category.comp_id] using
      lambdaRestrictionSourceMap_commutes coh i j hij X)

end KIP126.Synthetic.Context
