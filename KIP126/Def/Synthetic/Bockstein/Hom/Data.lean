module

public import KIP126.Def.Synthetic.Bockstein.Maps.Data
public import KIP126.Def.Synthetic.QuotientRestrictions.Data
public import KIP126.Def.Synthetic.Sphere.Shift.Data

@[expose] public section

/-!
The actual maps on bigraded homotopy induced by quotient inclusions,
λ-power quotient restrictions and the finite Bockstein arrow. The Bockstein
target is regraded by the specified additive suspension equivalence.
-/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Postcompose with the actual quotient inclusion. -/
noncomputable def inclHom (A : Syn) (q : ℕ) (n w : ℤ) :
    BiHom n w A →+ BiHom n w (XModLambdaN A q) :=
  Preadditive.rightComp (Smn n w) (XModLambdaN.incl A q)

/-- Postcompose with the actual Bockstein arrow, before regrading its target. -/
noncomputable def betaPostcompose (A : Syn) (q : ℕ) (n w : ℤ) :
    BiHom n w (XModLambdaN A q) →+
      BiHom n w
        (((SyntheticCategory.biShift (0, -(q : ℤ))).obj (XModLambdaN A 1))⟦(1 : ℤ)⟧) :=
  Preadditive.rightComp (Smn n w) (beta A q)

/-- The same Bockstein on actual homotopy groups, with its explicit
ordinary and weight suspension transport. -/
noncomputable def betaHom (A : Syn) (q : ℕ) (n w : ℤ) :
    BiHom n w (XModLambdaN A q) →+
      BiHom (n - 1) (w + (q : ℤ)) (XModLambdaN A 1) :=
  (biSuspensionHomEquiv n w (q : ℤ) (XModLambdaN A 1)).toAddMonoidHom.comp
    (betaPostcompose A q n w)

/-- Postcompose with the cofiber map of the actual λ-power factorization.
No freely supplied tower restriction is used. -/
noncomputable def restrictionHom (coh : BiShiftCoherence Syn) (A : Syn)
    (i j : ℕ) (hij : i ≤ j) (n w : ℤ) :
    BiHom n w (XModLambdaN A j) →+ BiHom n w (XModLambdaN A i) :=
  Preadditive.rightComp (Smn n w) (XModLambdaN.restriction coh A i j hij)

/-- Restrict a finite λ-power lift to the actual first quotient. -/
noncomputable def firstRestrictionHom (coh : BiShiftCoherence Syn) (A : Syn)
    (q : ℕ) (hq : 1 ≤ q) (n w : ℤ) :
    BiHom n w (XModLambdaN A q) →+ BiHom n w (XModLambdaN A 1) :=
  restrictionHom coh A 1 q hq n w

end KIP126.Synthetic.Bockstein
