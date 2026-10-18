module

import KIP126.Literature

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
open KIP126.Literature.Standard

-- Zero is allowed in finite lifting; q > 0 is still a mathematical premise.
example (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : ReachesPage model.classical.sphere (q+1) (s,t) x) :
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZero .sphere) q),
      a ≫ (model.quotients.tower (nuZero .sphere)).rho 1 q hq = firstLabel .sphere s t x :=
  (bhs_finite_lift .sphere q hq s t x).mp hx

-- Source completeness is retained, while its fixed-object comparison is a
-- separately tracked upstream theorem; neither asks for a result delivery.
example (products : HasProductsOfShape ℕ Spectrum)
    (h : BHSObjectApplicability products (SphereSpectrum (C := Spectrum))) :
    PermanentLiftAt .sphere := bhs_permanent_lift .sphere products h

example : PermanentLiftAt .sphere := selected_permanent_lift .sphere

example (products : HasProductsOfShape ℕ Spectrum) : True := by
  fail_if_success have h : PermanentLiftAt .sphere := bhs_permanent_lift .sphere products
  trivial

example (r : ℕ) (hr : 1 ≤ r) :
    SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔ quotientClass r (etaThetaSquare bxTheta5) = 0 :=
  bx_finite r hr

example : model.H6SquarePermanent ↔ lambdaEtaThetaSquare bxTheta5 = 0 := bx_untruncated

example : Theta5Detected bxTheta5 ∧ bxTheta5 + bxTheta5 = 0 :=
  ⟨bx_theta_label, bx_order_two⟩

example (s t : ℤ) (hpos : 0 < t-s) (hline : t-s < 2*s-3) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := sphereVanishing s t hpos hline

example (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t) :
    Epi (KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht) :=
  weight_epi X s t w₁ w₂ hw ht

example (X : ClassicalObject) (n : ℕ) (hn : 0 < n) (s t w : ℤ)
    (h : 0 ≤ t-w ∧ t-w < n) :
    IsIso ((model.family.quotientProjection
      (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap 2 (s,t,w)) :=
  finite_quotient_retained X n hn s t w h

#check nu_cofiber
#check lift
#check triangle_lift
#check nuCofiber_distinguished
#check eInfinity_lambda_finite
#check eInfinity_finite_labels
