module

public import KIP126.Def.Literature.Classical
public import Mathlib.CategoryTheory.Monoidal.Mon

/-! Source results beyond the old axiom inventory: the positive-stem
Adams vanishing line, one-line d₂, and BMQ/IWX/BR21 detector data.
Adapted from the fixed bbac1fc05843 Literature delivery (Apache-2.0).
The detector is the one in D, compared to this very source and ring unit. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public def SphereVanishingLine : Prop :=
  ∀ s t : ℤ, 0 < t-s → t-s < 2*s-3 → Subsingleton (D.classical.sphere.Page 2 (s,t))

public def classicalTwo : HomotopyGroup (C := C) 0 SphereSpectrum :=
  (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _)

/-- This target is the actual h₀ times the standard square. -/
public def oneLineTarget (j : ℕ) : D.classical.sphere.Page 2
    (3, 1+((2^(j-1+1) : ℕ) : ℤ)) :=
  D.sphereAlgebra.product (1,1) (2,((2^(j-1+1) : ℕ) : ℤ))
    (D.standardClasses.standardHi 0) (D.standardClasses.standardHiSquare (j-1))

public structure ClassicalRangeResults : Prop where
  sphereVanishing : SphereVanishingLine D
  two_detection : ClassicalDetects (D.classicalConvergence .sphere) (1,1)
    (D.standardClasses.standardHi 0) (classicalTwo (C := C))
  adamsOneLine_d2 : ∀ (j : ℕ), 4 ≤ j →
    HasNonzeroDifferential D.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (D.standardClasses.standardHi j) (oneLineTarget D j)

public def classicalSphereProduct {m n : ℤ}
    (x : HomotopyGroup (C := C) m SphereSpectrum)
    (y : HomotopyGroup (C := C) n SphereSpectrum) :
    HomotopyGroup (C := C) (m+n) SphereSpectrum :=
  (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫ (shiftFunctor C n).map x ≫ y

public structure TmfSourceData (B : TmfBindings D) where
  algebra : MonObj B.source
  algebra_unit : algebra.one = B.sourceUnit
  convergence : ClassicalTowerConvergence D.classicalTower B.source
  kappaBar : HomotopyGroup (C := C) 20 SphereSpectrum
  wClass : HomotopyGroup (C := C) 45 SphereSpectrum
  v2Sixteen : (D.classical.obj B.source).Page 2 (16,112)
  betaGFour : (D.classical.obj B.source).Page 2 (19,114)

public def TmfSourceData.high125 {B : TmfBindings D} (S : TmfSourceData D B) :
    HomotopyGroup (C := C) 125 SphereSpectrum :=
  classicalSphereProduct
    (classicalSphereProduct (classicalSphereProduct S.kappaBar S.kappaBar)
      (classicalSphereProduct S.kappaBar S.kappaBar)) S.wClass

/-- Only the supplied product κ̄⁴w is asserted nonzero under the source
unit. This does not assert nonvanishing for every homotopy representative. -/
public structure TmfSourceResults {B : TmfBindings D} (S : TmfSourceData D B) : Prop where
  connective : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n B.source)
  finiteModTwoType : ∀ n : ℤ, Finite (ModTwoHomology D.coefficients n B.source)
  g_nonzero : B.g ≠ 0
  g_unique : ∀ x : D.classical.sphere.Page 2 (4,24), x ≠ 0 → x = B.g
  delta_nonzero : B.deltaH1g ≠ 0
  delta_unique : ∀ x : D.classical.sphere.Page 2 (9,54), x ≠ 0 → x = B.deltaH1g
  vanishing62 : ∀ x : HomotopyGroup (C := C) 62 B.source, x = 0
  low_filtration63 : ∀ s : ℤ, s ≤ 0 →
    Subsingleton ((D.classical.obj B.source).Page 2 (s,63+s))
  kappaBar_detection : ClassicalDetects (D.classicalConvergence .sphere) (4,24) B.g S.kappaBar
  w_detection : ClassicalDetects (D.classicalConvergence .sphere) (9,54) B.deltaH1g S.wClass
  high125_nonzero : S.high125 D ≫ B.sourceUnit ≠ 0
  br21 : HasDifferential (D.classical.obj B.source) 3 (16,112) (19,114)
    S.v2Sixteen S.betaGFour

/-- The source differential transfers along its actual detector isomorphism.
No second comparison of pages or extra nonzero-survival premise is chosen. -/
public theorem TmfSourceResults.detector_d3 {B : TmfBindings D}
    {S : TmfSourceData D B} (R : TmfSourceResults D S) :
    HasDifferential (D.classical.obj D.auxiliary.detector) 3 (16,112) (19,114)
      ((D.classical.map B.sourceIso.hom).pageMap 2 (16,112) S.v2Sixteen)
      ((D.classical.map B.sourceIso.hom).pageMap 2 (19,114) S.betaGFour) := by
  exact (D.classical.map B.sourceIso.hom).hasDifferential R.br21

end
end KIP126.Literature
