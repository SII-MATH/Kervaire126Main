module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements

@[expose] public section

/-! Cited classical and synthetic Adams conclusions, with their original
objects, hypotheses and comparison conditions. Their truth is supplied by
the literature hypotheses; this module introduces no proof or new axiom. -/

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Pstrągowski/BHS lifting and triangle conditions use this very ν.
This abbreviation states those properties without asserting their truth. -/
abbrev SyntheticLiftTheorems := KIP126.Synthetic.NuCofiberAndLiftTheorems H D.nu

/-- BHS A.8 / LWX Theorem 3.6: the source λᵏx and target
λ^(k+r-1)y have the same weight. This literature statement compares the
specified differentials; it does not define a map from the entire classical
sequence to every synthetic weight. -/
def ClassicalSyntheticDifferentialComparison : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : E2 H (X.obj D.hopfAndDetector) s t)
      (y : E2 H (X.obj D.hopfAndDetector) (s + r) (t + r - 1)),
    KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) r
      (s,t) (s+r,t+r-1) x y →
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)))) r
      (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1) : ℕ))
      (D.nuE2 X a s t k x) (D.nuE2 X a (s+r) (t+r-1) (k+(r-1)) y)

/-- Identify the geometric Hopf maps used by the extension laws with standard classes
and to the actual synthetic η used in C₅. These are explicit literature
identifications, not consequences inferred merely from the maps' names. -/
def HopfClassComparison (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,2)
    (Sphere.Internal.hi H M 1) D.hopfAndDetector.etaMap ∧
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,4)
    (Sphere.Internal.hi H M 2) D.hopfAndDetector.nuMap ∧
  ∃ he : normalizedExponent H D.hopfAndDetector.etaMap = 1,
    η = (etaSourceIso D he).hom ≫
      (D.normalizedMap (.shift 1 .sphere) .sphere D.hopfAndDetector.etaMap).map ≫ D.nu.unitIso.hom

/-- The original distinguished-choice BX condition, before the LWX
normalization and arbitrary-choice deductions. BX Proposition 7.19. -/
abbrev BXThetaCriterion (η : BiHom 1 2 (S_0_0 : Syn)) (θ : BiHom 62 64 (S_0_0 : Syn)) :=
  BJMOriginalCriterion H M D.sphereFirstQuotient η θ

/-- Actual order-two statement used before Moss; no presentation of π₆₂
as an unrelated abstract group is substituted. Xu/IWX, cited by LWX 7.16. -/
def OrderTwo62 : Prop :=
  ∀ α : HomotopyGroup (C := C) 62 SphereSpectrum, α + α = 0

/-- The local sphere form of the Moss implication needed in LWX Lemma 7.16.
Source: Moss Theorem 1.2; crossing convention also IWX Definition 2.15 and
Theorem 2.16. No claim of zero indeterminacy is hidden in the conclusion:
there exists a permanent defining-system value detecting a bracket member.
The three detection and two null-composition hypotheses are explicit. -/
def ThetaBMossConvergence : Prop :=
  ∀ (B : E2 H SphereSpectrum 8 70)
    (θ β : HomotopyGroup (C := C) 62 SphereSpectrum)
    (two : HomotopyGroup (C := C) 0 SphereSpectrum),
    two = (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _) →
    TowerDetection.Detects (D.classicalConvergence .sphere) (2,64)
      (Sphere.Internal.hiSquare H M 5) θ →
    TowerDetection.Detects (D.classicalConvergence .sphere) (1,1)
      (Sphere.Internal.hi H M 0) two →
    TowerDetection.Detects (D.classicalConvergence .sphere) (8,70) B β →
    θ + θ = 0 → β + β = 0 →
    (ThetaBMassey M B).Nonempty →
    ¬ SphereMossCrossing (H := H) 3 (3,65) →
    ¬ SphereMossCrossing (H := H) 3 (9,71) →
    TowerDetection.ResidualInjectivity H.unit (SphereSpectrum (C := C)) →
    ∃ (z : E2 H SphereSpectrum 9 134)
      (ξ : HomotopyGroup (C := C) 125 SphereSpectrum),
      ThetaBMasseyDefiningSystem M B z ∧
      TowerDetection.Detects (D.classicalConvergence .sphere) (9,134) z ξ ∧
      ThetaBToda θ β ξ
end KIP126.Literature.AdamsSynthetic

/-! Classical literature hypotheses on the specified sphere Adams tower.
The following predicates retain the exact detection, order and filtration
conditions from the cited results; they do not prove those results. -/
namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BJM (1984), or Xu Corollary 1.3: an order-two θ₅ exists.
The nonzero-survival clause prevents a zero representative from fulfilling
existence merely because `Detects` permits a zero associated-graded class. -/
def Theta5Existence : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (2,64) (Sphere.Internal.hiSquare H M 5) ∧
  ∃ θ, ClassicalTheta D θ ∧ θ + θ = 0

/-- IWX's classical 62-stem computation: every element has exponent two.
Xu's existence of ONE order-two θ₅ alone does not imply this assertion. -/
abbrev Stem62ExponentTwo := KIP126.Literature.AdamsSynthetic.OrderTwo62 (C := C)

/-- The exact part of IWX's Adams filtration calculation used in LWX
Lemma 7.10: two classical h₅²-detected choices differ in filtration ≥ 6.
This is a consequence of the PREVIOUSLY published 62-stem computation,
not the synthetic choice-independence lemma proved in the present paper. -/
def Theta5FiltrationGap : Prop :=
  ∀ θ θ' : HomotopyGroup (C := C) 62 SphereSpectrum,
    ClassicalTheta D θ → ClassicalTheta D θ' →
    θ - θ' ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 6 62

/-- Detection of the actual degree-zero multiplication-by-two map. Source:
the classical Adams 0-stem, with h₀ the standard Milnor generator. -/
def TwoDetection : Prop :=
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,1)
    (Sphere.Internal.hi H M 0)
    ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))

/-- Adams' Hopf classes, including identification of the selected synthetic
η with the SAME normalized geometric η map. The equality is a comparison with the classical Hopf map; the name of `etaMap` alone proves nothing. -/
def HopfClassTheorems (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η ∧ KIP126.Literature.AdamsSynthetic.HopfClassComparison D η ∧
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (1,2) (Sphere.Internal.hi H M 1) ∧
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (1,4) (Sphere.Internal.hi H M 2)

end KIP126.Literature.AdamsSynthetic


namespace KIP126.Literature.AdamsSynthetic
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BX Proposition 7.19 and its proof, at ONE common source choice.
All three clauses use that same θ₅ and the η fixed in `ClassicalTheorems`.
The original finite formula uses ηθ₅² modulo λ^r. The total-boundary formula
and the untruncated iff are explicitly in the proof of BX Proposition 7.19.
The LWX normalization to ληθ₅² modulo λ^(r+1), and extension to arbitrary
choices, remain paper deductions; they are deliberately absent here. -/
def BXDistinguishedThetaTheorem (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  ∃ θ : BiHom 62 64 (S_0_0 : Syn),
    BJMOriginalCriterion H M D.sphereFirstQuotient η θ ∧
    BJMDistinguishedThetaBoundaryIdentity H M D.sphereFirstQuotient η θ ∧
    BJMUntruncatedCriterion H M η θ
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS Theorem A.1(1): vanishing through d_q iff a lift to νX/λ^q
exists. Membership in Z_q permits a boundary or zero label; `SurvivesTo`
would incorrectly demand nonzero. All restrictions are D's actual ρ. -/
def FiniteLiftCriterion : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t),
    (x ∈ PageRepresentatives.cycles H (X.obj D.hopfAndDetector) q (s,t) ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
        a ≫ (D.quotientTower (nuZero D X)).rho 1 q hq = firstLabel D X s t x)

/-- BHS A.1(1c): choose a lift whose boundary represents the differential.
The target is stated modulo the ACTUAL classical page boundaries by
`HasDifferential`; an arbitrary lift need not have this property. The sign
in BHS disappears in the mod-2 E₂ group, not in integral homotopy groups. -/
def BocksteinDifferential : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t),
    x ∈ PageRepresentatives.cycles H (X.obj D.hopfAndDetector) q (s,t) →
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
      a ≫ (D.quotientTower (nuZero D X)).rho 1 q hq = firstLabel D X s t x ∧
      KIP126.SpectralSequence.HasDifferential
        (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
        (q+1) (s,t) (s+q+1,t+q) x (bocksteinLabel D X q hq s t a)

/-- BHS A.1(2): lift a permanent cycle through the untruncated νX.
This is not an assertion that every E₂ label is a permanent cycle. -/
def PermanentLiftCriterion : Prop :=
  ∀ (X : ClassicalObject) (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t),
    (x ∈ PageRepresentatives.permanentCycles H (X.obj D.hopfAndDetector) (s,t) ↔
      ∃ a : BiHom (t-s) t (nuZero D X),
        quotientClass 1 a = firstLabel D X s t x)

/-- BHS A.8, including the converse on labeled representatives.
These are the existing differentials on the same family, not a newly
postulated differential function. Multiplication by λ changes weight only. -/
def DifferentialRigidity : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : E2 H (X.obj D.hopfAndDetector) s t)
      (y : E2 H (X.obj D.hopfAndDetector) (s+r) (t+r-1)),
    (KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) r
      (s,t) (s+r,t+r-1) x y ↔
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)))) r
      (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1) : ℕ))
      (D.nuE2 X a s t k x) (D.nuE2 X a (s+r) (t+r-1) (k+(r-1)) y))

/-- The λ-localization kernel criterion on the specified objects: only the objects in
`SyntheticObject` and their displayed bidegrees are quantified. Compactness
belongs to the FULL source category; no hypercomplete sphere is asserted
compact. The adjunction, λ and realization comparisons are separate hypotheses,
stated below as `SyntheticCompletionAdjunction` and `RealizationKernelComparison`. -/
def RealizationKernel : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ) (a : BiHom m w (X.obj D.nu D.hopfAndDetector)),
    (D.recovery.realization.map a = 0 ↔ ∃ k : ℕ, lambdaMultiply k a = 0)

/-- BHS `cor:tau-surj`: Adams filtration equals λ-Bockstein filtration.
The inequality makes the exponent nonnegative. It says nothing about
the filtration of a particular θ₅² or the value of a particular product. -/
def FiltrationLambda : Prop :=
  ∀ (X : ClassicalObject) (m w s : ℤ) (h : w - m ≤ s),
    ∀ a : BiHom m w (D.nu.functor.obj (X.obj D.hopfAndDetector)),
    (FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a ↔
      ∃ b : BiHom m (m+s) (D.nu.functor.obj (X.obj D.hopfAndDetector)),
        homotopyRegrade rfl (by rw [Int.toNat_of_nonneg (by omega)]; omega)
          (lambdaMultiply (m+s-w).toNat b) = a)

/-- Untruncated lifting at ONE source object. BHS A.1(2) is applied only
after its nilpotent-completeness and strong-convergence hypotheses are supplied. -/
def BHSPermanentLiftAt (X : C) : Prop :=
  ∀ (s t : ℤ) (x : E2 H X s t),
    (x ∈ PageRepresentatives.permanentCycles H X (s,t) ↔
      ∃ a : BiHom (t-s) t
        ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
        quotientClass 1 a = bhsFirstLabel D X s t x)

/-- BHS cor:tau-surj on a specified source object. -/
def BHSFiltrationLambdaAt (X : C) : Prop :=
  ∀ (m w s : ℤ) (h : w-m ≤ s) (a : BiHom m w (D.nu.functor.obj X)),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a ↔
      BHSLambdaDivisible D X m w s h a

/-- The remaining zero region in BHS A.8's E₂ formula. M already fixes
the nonzero-weight comparison D.nuE2; this rules out extra classes above
that region instead of silently ignoring them. -/
def E2WeightVanishing : Prop :=
  ∀ (X : ClassicalObject) (a s t w : ℤ), t+a < w →
    Subsingleton ((D.family.obj ((SyntheticCategory.biShift (0,a)).obj
      (D.nu.functor.obj (X.obj D.hopfAndDetector)))).E₂ (s,t,w))

/-- BHS `SynRevAdams.tex`, `cor:synth-ctau-ASS` (1),(3), in the paper's
weight convention: for each positive quotient length q, every finite page
E_r (r >= 2) is zero outside 0 <= t-w < q. The E-infinity assertion is
separately part of `EInftyPresentation`. This is a statement about the actual
finite lambda quotient and its actual Adams pages, not about lambda^q acting
as zero on all of its homotopy groups. No completeness hypothesis on X is
needed for this finite-quotient source result. -/
def FiniteQuotientPageVanishing : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ), 0 < q → ∀ (r s t w : ℤ), 2 ≤ r →
    (t < w ∨ (q : ℤ) ≤ t-w) →
      Subsingleton ((D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).Page r (s,t,w))

end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- The source square and boundary relation selected from May (2001), TC3
(author PDF pp.12–13). The lifting field is the homotopy-group consequence
of the `(j₁,j₂)` pushpull square in Lemma 4.6 (p.14). This is precisely the
part of that source data used here, not a definition of the full TC3 axiom.

The negative sign is essential: TC3 identifies the two paths through
`−id ∧ h′` and `h ∧ id`. The fixed CommShift witnesses above identify their
common suspension target. No unsigned boundary formula is asserted. -/
structure MayPushpullData (B : MayContext Syn)
    (T U : HoCofiberSequence (C := Syn)) where
  vertex : Syn
  j1 : vertex ⟶ T.X ⊗ U.Z
  j2 : vertex ⟶ T.Y ⊗ U.Y
  j3 : vertex ⟶ T.Z ⊗ U.X
  square : j1 ≫ (T.f ▷ U.Z) = j2 ≫ (T.Y ◁ U.g)
  other_square : j2 ≫ (T.g ▷ U.Y) = j3 ≫ (T.Z ◁ U.f)
  boundary : letI := B.leftShift; letI := B.rightShift
    letI := B.leftExact; letI := B.rightExact
    j1 ≫ (U.map (tensorLeft T.X)).h = -(j3 ≫ (T.map (tensorRight U.X)).h)
  lift : ∀ (n : ℤ) (a : HomotopyGroup n (T.X ⊗ U.Z))
      (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    a ≫ (T.f ▷ U.Z) = b ≫ (T.Y ◁ U.g) →
    ∃ v : HomotopyGroup n vertex, v ≫ j1 = a ∧ v ≫ j2 = b

/-- The signed elementwise consequence of TC3 and Lemma 4.6. Both boundary
classes lie in the same actual homotopy group. -/
def MayContext.SignedBoundary (B : MayContext Syn) : Prop :=
  letI := B.leftShift; letI := B.rightShift
  letI := B.leftExact; letI := B.rightExact
  ∀ (T U : HoCofiberSequence (C := Syn)) (n : ℤ)
    (a : HomotopyGroup n (T.X ⊗ U.Z))
    (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b →
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      connectingHomomorphism (U.map (tensorLeft T.X)) n a =
        -(connectingHomomorphism (T.map (tensorRight U.X)) n c)

end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Intrinsic identities of the two source labels, without choosing an
arbitrary nonzero class or relying on its name. The classical E2 groups
(4,24) and (9,54) each have exactly one nonzero element. Source: IWX v3,
`cor:main-Adams`, and the cited 2022 Zenodo v1 classical E2 chart CSV,
rows 59 (`g`, stem 20, AF 4) and 275 (`D h1 g`, stem 45, AF 9).
The chart's `D` denotes Delta. These finite prior calculations make the
source labels unique even when the source result is supplied existentially. -/
def TmfDetectionClasses.Standard (G : TmfDetectionClasses H) : Prop :=
  G.g ≠ 0 ∧ (∀ x : E2 H SphereSpectrum 4 24, x ≠ 0 → x = G.g) ∧
  G.delta_h_1_mul_g ≠ 0 ∧
    (∀ x : E2 H SphereSpectrum 9 54, x ≠ 0 → x = G.delta_h_1_mul_g)

end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Moss (1970), Theorem 1.2, in the precise local specialization used by
LWX Lemma 7.16. The defining systems, two null products, two no-crossing
conditions and residual-tower condition remain explicit hypotheses.
It asserts existence of a detected bracket member, not that every member
is permanent or that the bracket has zero indeterminacy. The statement and
crossing convention were also checked against Belmont--Kong (2021),
Theorem 1.1 / 4.11 and Definition 2.10. Moss's original scan was unavailable;
the source inventory does not advertise it as independently read. -/
abbrev MossConvergenceTheorem := KIP126.Literature.AdamsSynthetic.ThetaBMossConvergence D

/-- The residual-tower hypothesis for the selected complete classical
sphere. This is an applicability obligation for the Moss source theorem,
not a computational no-crossing or Massey-value assertion. -/
abbrev MossTowerResidualInjectivity :=
  TowerDetection.ResidualInjectivity H.unit (SphereSpectrum (C := C))
end KIP126.Literature.AdamsSynthetic

