module

public import KIP126.Def.Literature

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] {D : Model C Syn}

-- A finite lift consumes the actual quotient restriction, without nonzero.
example (L : LiteratureInterface D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (hx : ReachesPage (D.classical.obj (X.obj D.auxiliary)) (q+1) (s,t) x) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
      a ≫ (D.quotients.tower (nuZero D X)).rho 1 q hq = firstLabel D X s t x :=
  (L.results.bhs.finite_lift X q hq s t x).mp hx

-- The untruncated source theorem cannot silently discard applicability.
example (R : BHSResults D) (X : ClassicalObject) (products : HasProductsOfShape ℕ C)
    (h : BHSObjectApplicability D products (X.obj D.auxiliary)) : PermanentLiftAt D X := by
  fail_if_success exact R.permanent_lift X products
  exact R.permanent_lift X products h

-- The full source delivery supplies the selected-object transport separately.
example (L : LiteratureInterface D) (X : ClassicalObject) : PermanentLiftAt D X :=
  L.results.selectedComparisons.permanent_lift X

-- BR21 keeps the actual detector map, with no extra nonzero-survival claim.
example (L : LiteratureInterface D) :
    HasDifferential (D.classical.obj D.auxiliary.detector) 3 (16,112) (19,114)
      ((D.classical.map L.bindings.tmf.sourceIso.hom).pageMap 2 (16,112)
        L.bindings.tmfSource.v2Sixteen)
      ((D.classical.map L.bindings.tmf.sourceIso.hom).pageMap 2 (19,114)
        L.bindings.tmfSource.betaGFour) := L.results.tmf.detector_d3 D

-- BX gives one correlated choice; the vanishing argument is still needed.
example (L : LiteratureInterface D) :
    ∃ θ : BiHom 62 64 (S_0_0 : Syn),
      Theta5Detected D θ ∧ θ+θ=0 ∧
      (D.H6SquarePermanent ↔ lambdaEtaThetaSquare L.bindings.eta θ = 0) := by
  obtain ⟨θ,hθ⟩ := L.results.bx
  exact ⟨θ,hθ.theta_label,hθ.order_two,hθ.untruncated⟩

-- The original positive-stem restriction retains the h₀ tower in stem zero.
example (L : LiteratureInterface D) (s t : ℤ) (hp : 0 < t-s) (hv : t-s < 2*s-3) :
    Subsingleton (D.classical.sphere.Page 2 (s,t)) := L.results.classicalRange.sphereVanishing s t hp hv
