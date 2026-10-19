module

import KIP126.Literature

/-! Literature theorems are used through the ordinary public import. The
lambda-inversion comparison remains explicit mathematical input. -/

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
open KIP126.Literature.Standard

section LambdaInversionConsumer
open KIP126.Kervaire.Route KIP126.Synthetic.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)

/-- Detection transports the specified representative itself, including zero
or boundary labels; no nonzero or essentiality condition is supplied. -/
example (R : KIP126.Literature.RealizationCoordinates D)
    (U : SyntheticObject) (X : ClassicalObject)
    (K : KIP126.Literature.LambdaInversionAdamsObjectComparison D R U X)
    (s t w : ℤ)
    (x : (D.family.obj (U.obj D.nu D.auxiliary)).E₂ (s,t,w))
    (β : BiHom (t-s) w (U.obj D.nu D.auxiliary))
    (hβ : Detects (D.convergence U) (s,t,w) x β) :
    ClassicalDetects (D.classicalConvergence X) (s,t) (K.e2Map w (s,t) x)
      ((R.sphere (t-s) w).hom ≫ D.recovery.realization.map β ≫ K.target.hom) :=
  K.detects s t w x β hβ

end LambdaInversionConsumer

example (T : KIP126.Kervaire.Route.TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0 < q) :
    let V := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (V.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN V.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (V.obj₂⟦(1:ℤ)⟧) q ≫ esusp.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map V.mor₂ q)
        (XModLambdaN.map V.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) q ≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum :=
  normalized_finite_quotient_horizontal_row T he hT q hq

example : theta5 + theta5 = 0 := theta5_order_two

example : ClassicalTheta5Detected theta5 := theta5_detection

example : NonzeroSurvival model.classical.sphere (1,2)
    (model.standardClasses.standardHi 1) := eta_permanent

example (j : ℕ) (hj : 4 ≤ j) :
    HasNonzeroDifferential model.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (model.standardClasses.standardHi j) (oneLineTarget j) :=
  adamsOneLine_d2 j hj

example : g ≠ 0 := g_nonzero

example : HasDifferential (model.classical.obj model.auxiliary.detector)
    3 (16,112) (19,114)
    ((model.classical.map tmfIso.hom).pageMap 2 (16,112) tmfV2Sixteen)
    ((model.classical.map tmfIso.hom).pageMap 2 (19,114) tmfBetaGFour) := detector_d3

example : sphereFirstQuotient 1 2 (quotientClass 1 eta) =
    model.standardClasses.standardHi 1 := eta_label

example : sphereFirstQuotient 1 64 h6FirstQuotient =
    model.standardClasses.standardH6 := h6FirstQuotient_label

example : ∃ y : model.classical.sphere.Page 2 (5,19),
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (hiProduct 0 4) y := iwx_h0_h4_d3

#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Literature.ClassicalResults
#check_failure KIP126.Literature.Standard.literature
#check_failure KIP126.Literature.Standard.mainTheorem
#check_failure KIP126.Literature.Standard.theta5_indeterminacy_AF_ge_6
