module

public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems
public import KIP126.Literature.Source
public import KIP126.Main.Computation.Tmf.Conclusions

@[expose] public section

/-! Applications of the literature theorems to a common Adams–synthetic model.
The comparison conditions specify how the source objects realize this model. -/

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- The classical θ₅ and Hopf-class theorems used in Section 7. -/
structure ClassicalTheorems (η : BiHom 1 2 (S_0_0 : Syn)) : Prop where
  theta5_exists : Theta5Existence D
  stem62_exponent_two : Stem62ExponentTwo (C := C)
  theta5_filtration_gap : Theta5FiltrationGap D
  two_detection : TwoDetection D
  hopf : HopfClassTheorems D η


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

/-- Transport the BHS source theorems along the specified completion
comparison, using the realization-kernel theorem on the same objects. -/
def SyntheticSourceTheorems.toComparisonTheorems (S : SyntheticSourceTheorems D)
    (Q : BHSCompletionData D) (hQ : BHSCompletionApplicability D Q)
    (B : BHSCompletionComparison D Q)
    (kernel : RealizationKernel D) : SyntheticComparisonTheorems D where
  lifts := S.lifts
  finite_lift := S.finite_lift
  bockstein := S.bockstein
  permanent_lift := by
    intro X s t x
    exact (B.permanent_cycles X s t x).trans
      ((S.permanent_lift (Q.completed X) Q.products (hQ.source X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)).trans
        (B.first_quotient_image X s t x))
  differentials := S.differentials
  eInfty := S.eInfty
  realization_kernel := kernel
  filtration_lambda := by
    intro X m w s h a
    exact (B.filtration X m w s a).trans
      ((S.filtration_lambda (Q.completed X) Q.products (hQ.source X) m w s h
        (a ≫ D.nu.functor.map (Q.map X))).trans
        (B.lambda_divisibility X m w s h a))
  e2_weight_vanishing := S.e2_weight_vanishing
  finite_quotient_page_vanishing := S.finite_quotient_page_vanishing


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- Ordinary transport along the displayed source equalities. The sole
synthetic premise is supplied separately, so the classical source theorem
does not assert it or normalized-map compatibility. -/
theorem classicalTheoremsOfSource (D : AdamsComparison H M Syn) (η : BiHom 1 2 (S_0_0 : Syn))
    (S : ClassicalHopfThetaClasses H) (hS : ClassicalSourceResults M S)
    (B : ClassicalHopfComparison D η S) (hη : EtaChoice M D.toAdamsComparisonData η) :
    ClassicalTheorems D η where
  theta5_exists := ⟨hS.h5Square_permanent, S.theta5,
    by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using hS.theta5_detection,
    hS.theta5_order_two⟩
  stem62_exponent_two := hS.stem62_exponent_two
  theta5_filtration_gap := by
    intro a b ha hb
    exact hS.theta5_filtration_gap a b
      (by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using ha)
      (by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using hb)
  two_detection := by simpa [TwoDetection, B.convergence, ClassicalObject.obj] using hS.two_detection
  hopf := by
    refine ⟨hη, ?_, hS.eta_permanent, hS.nu_permanent⟩
    refine ⟨?_, ?_, B.normalized_eta⟩
    · simpa [B.convergence, B.eta, ClassicalObject.obj] using hS.eta_detection
    · simpa [B.convergence, B.nu, ClassicalObject.obj] using hS.nu_detection


end KIP126.Literature.AdamsSynthetic


namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Low-degree ring relations and Toda-bracket comparisons. The ring relations
and secondary-operation comparisons are supplied by `TodaSourceResults` and
`TodaComparisonRelations`, respectively. The latter uses Toda 1962, Theorem 3.6 and
IWX §6; the C-motivic result IWX `cor:2-symmetric` requires comparison before
application in the synthetic category. The final field asserts bracket
membership; the high-degree indeterminacy calculation belongs to Main. -/
structure TodaRelations (η : BiHom 1 2 (S_0_0 : Syn)) where
  h0 : BiHom 0 1 (S_0_0 : Syn)
  h0_label : D.sphereFirstQuotient 1 1 (quotientClass 1 h0) = Sphere.Internal.hi H M 0
  lambda_h0 : lambdaMultiply 1 h0 = syntheticTwo
  h0_eta : sphereProduct h0 η = 0
  /-- η² belongs to <[h₀],η,[h₀]>. We do not replace a Toda set by
  a selected value; the low indeterminacy vanishing is a separate field. -/
  eta_squared : TripleToda h0 η h0
    (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) η η)
  /-- Consequence of the BHS low-stem ring: [h₀]·π_(2,3)=0.
  Together with graded commutativity it kills both indeterminacy summands
  of the preceding LOW bracket, not those of <2,θ₅,2>. -/
  low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct h0 a = 0
  /-- The symmetric Toda identity in stem 62 used in Section 7.
  No claim that the bracket is a singleton or that θ is order two is made. -/
  symmetric_two : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (lambdaMultiply 2 (sphereProduct η θ))

/-- Internal source-to-model application: actual secondary Toda relations on
the same sphere and chosen h₀,η. No high-degree indeterminacy is removed. -/
structure TodaComparisonRelations (η : BiHom 1 2 (S_0_0 : Syn))
    (S : SyntheticH0Class (Syn := Syn)) : Prop where
  eta_squared : TripleToda S.h0 η S.h0
    (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) η η)
  symmetric_two : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (lambdaMultiply 2 (sphereProduct η θ))

/-- Combine the source ring relations with the proved secondary-operation
comparisons to obtain the synthetic Toda relations. -/
def todaRelationsOfSource (η : BiHom 1 2 (S_0_0 : Syn)) (S : SyntheticH0Class (Syn := Syn))
    (A : TodaSourceResults D η S) (P : TodaComparisonRelations η S) : TodaRelations D η where
  h0 := S.h0
  h0_label := A.h0_label
  lambda_h0 := A.lambda_h0
  h0_eta := A.h0_eta
  eta_squared := P.eta_squared
  low_indeterminacy := A.low_indeterminacy
  symmetric_two := P.symmetric_two


end
end KIP126.Literature.AdamsSynthetic



namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS A.1(2b),(3b). The same standard E₂ label detects the realized
class, and every specified detected class has an appropriate lift.
Neither clause replaces an arbitrary E₂ class by a later-page element. -/
structure RealizationDetection (R : RealizationCoordinates D) : Prop where
  /-- BHS A.1(2a): nonzero survival to E_(r+1) controls the lifetime
  of EVERY lift of a permanent cycle. The exponent is r-1, not r. -/
  lifetime : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 H (X.obj D.hopfAndDetector) s t) (a : BiHom (t-s) t (nuZero D X)),
    x ∈ PageRepresentatives.permanentCycles H (X.obj D.hopfAndDetector) (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
      (r+1) (s,t) x → quotientClass 1 a = firstLabel D X s t x →
    lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t) (a : BiHom (t-s) t (nuZero D X)),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
      (s,t) x → quotientClass 1 a = firstLabel D X s t x →
    TowerDetection.Detects (D.classicalConvergence X) (s,t) x (realizeNuZero D R X a)
  prescribed_lift : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t) (α : HomotopyGroup (t-s) (X.obj D.hopfAndDetector)),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
      (s,t) x → TowerDetection.Detects (D.classicalConvergence X) (s,t) x α →
    ∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t x ∧ realizeNuZero D R X a = α
  /-- BHS A.1(3a): only SOME lift of a permanent boundary is torsion.
  It would be wrong to demand this of every lift. -/
  boundary_lift : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 H (X.obj D.hopfAndDetector) s t),
    y ∈ PageRepresentatives.permanentCycles H (X.obj D.hopfAndDetector) (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t y ∧ lambdaMultiply (r-1) a = 0

/-- Realization coordinates together with their homotopy detection properties. -/
structure RealizationDetectionData where
  coordinates : RealizationCoordinates D
  detection : RealizationDetection D coordinates


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Model applicability obligations, recorded separately from the source
statements. They do not assert the ν-extension constructed in LWX Lemma 7.19. -/
structure Applicability : Prop where
  nuCofiber : NuCofiberNormalization D


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfDetectionClasses H)

/-- Literature consequences and Main deductions for one model and η.
The tmf homotopy class and its computed detection use the same labels.
`applicability` records the comparisons identifying the source objects
with this model, including the chosen homotopy lifts. -/
structure AdamsSyntheticTheorems where
  classical : ClassicalTheorems D η
  bx : BXDistinguishedThetaTheorem D η
  synthetic : SyntheticComparisonTheorems D
  realization : RealizationDetectionData D
  algebra : CompatibleAdamsAlgebras D
  may : MayBoundaryFormula Syn
  toda : TodaRelations D η
  tmf : TmfDetectionTheorems D L
  applicability : Applicability D

/-- Comparison conditions for applying the source theorems to this model.
May's convergence theorem retains its sign, the Toda relations require
secondary-operation comparisons, and the realization-kernel theorem uses
the fixed realization comparison. The normalized cofiber triangle also
requires its multiplicative comparison. -/
structure SourceApplicability {background : AlgebraRealizationComparison D} (B : SourceComparisons D η L background) : Prop where
  bhsApplicability : BHSCompletionApplicability D B.bhsCompletion
  bhsComparison : BHSCompletionComparison D B.bhsCompletion
  realization : RealizationDetection D B.realization
  may : B.may.SignedBoundary
  toda : TodaComparisonRelations η B.todaSource
  realizationKernel : RealizationKernel D
  nuSource : NuCofiberSourceResults D B.nuSource
  nuCofiber : NuCofiberNormalization D

/-- Combine the source theorems, their comparisons and the tmf consequences
proved in Main. The stem-125 survival statement is one of these deductions;
it is not an additional external hypothesis. -/
def SourceTheorems.toAdamsSyntheticTheorems {background : AlgebraRealizationComparison D} {B : SourceComparisons D η L background} (A : SourceTheorems D η L B)
    (P : SourceApplicability D η L B) (tmf : TmfDetectionTheorems D L) : AdamsSyntheticTheorems D η L where
  classical := classicalTheoremsOfSource D η B.classicalSource A.classical
    B.hopfComparison B.synthetic_eta
  bx := A.bx
  synthetic := A.synthetic.toComparisonTheorems D B.bhsCompletion P.bhsApplicability
    P.bhsComparison P.realizationKernel
  realization := ⟨B.realization, P.realization⟩
  algebra := B.algebra.withCompatibility D B.quotientCompatibility
  may := { B.may with boundary := P.may }
  toda := todaRelationsOfSource D η B.todaSource A.toda P.toda
  tmf := tmf
  applicability := ⟨P.nuCofiber⟩


end KIP126.Literature.AdamsSynthetic
