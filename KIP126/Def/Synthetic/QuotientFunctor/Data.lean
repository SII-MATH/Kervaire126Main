module

public import KIP126.Def.Synthetic.QuotientMap.Functoriality.Proofs
public import KIP126.Def.Synthetic.QuotientMap.Proofs
public import KIP126.Def.Synthetic.QuotientRestrictions.Functoriality.Proofs

@[expose] public section

/-! The actual λ-power quotient functors and their restriction transformations.
Every object and component map is the existing chosen cofiber construction.
This does not construct the λ–ρ–δ triangles or a homotopy inverse limit.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The already specified `XModLambdaN` objects and maps form a functor under
the explicit identity and composition laws for that same cofiber choice. -/
noncomputable def XModLambdaN.functor (cofib : FunctorialCofiberCoherence Syn)
    (n : ℕ) : Syn ⥤ Syn where
  obj X := XModLambdaN X n
  map f := XModLambdaN.map f n
  map_id X := XModLambdaN.map_id cofib X n
  map_comp f g := XModLambdaN.map_comp cofib f g n

/-- The actual quotient inclusions, natural in the original synthetic object. -/
noncomputable def XModLambdaN.inclNatTrans (cofib : FunctorialCofiberCoherence Syn)
    (n : ℕ) : 𝟭 Syn ⟶ XModLambdaN.functor cofib n where
  app X := XModLambdaN.incl X n
  naturality _ _ f := XModLambdaN.incl_naturality f n

/-- The existing power-factorization cofiber maps form a natural transformation
from the `j`th quotient functor to the `i`th, for `i ≤ j`. -/
noncomputable def XModLambdaN.restrictionNatTrans
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.functor cofib j ⟶ XModLambdaN.functor cofib i where
  app X := XModLambdaN.restriction coh X i j hij
  naturality _ _ f := XModLambdaN.restriction_naturality coh cofib f i j hij

end KIP126.Synthetic.Context
