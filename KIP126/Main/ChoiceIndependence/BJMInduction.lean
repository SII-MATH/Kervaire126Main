module

public import KIP126.Def.AdamsSynthetic.Conditions.Predicates
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data
public import KIP126.Main.Computation.Lambda
import all KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
import all KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection
import all KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
import all KIP126.Main.SectionSeven.DifferentialCriterion.Dichotomy

@[expose] public section

section Predicate
open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : AdamsComparison H M Syn) (L : SphereAdamsClasses H)

namespace KIP126.Main.Stem126.BJMInduction
open KIP126.Kervaire
/-- The proposition expressing Theorem 7.3 and the choice independence
discussed in Remarks 7.4–7.5. It asks for the normalized criterion for every
admissible θ₅. The literature supplies the BX criterion at its source choice;
this definition supplies no proof of normalization or choice independence. -/
def any_choice_criterion (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η →
    ∀ θ, ThetaChoice M D.toAdamsComparisonData θ →
      BJMNormalizedFiniteCriterion H M η θ ∧
      BJMUntruncatedCriterion H M η θ
end KIP126.Main.Stem126.BJMInduction
end Predicate

/-! LWX Remarks 7.4–7.5, adapted from Kervaire126Main commits 53f42f9
and edbb648. The proof uses the same literature and computation witnesses,
and does not use the final permanence theorem. -/
namespace KIP126.Main.Stem126.BJMInduction
universe u v w
open KIP126.Classical.Adams KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits
open KIP126.SpectralSequence KIP126.SpectralSequence.FinitePageCalculus
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire
open KIP126.Kervaire.SyntheticTheta5 KIP126.Literature.AdamsSynthetic
open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126 KIP126.LinE2
open KIP126.Main.SectionSeven.DifferentialCriterion
open private theta_square_choice_theta_choice_filtration_gap_of_pages
  theta_square_choice_theta_choice_finite_pages theta_square_choice_theta_square_difference
  theta_square_choice_theta_degree_order_two
  from KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
open private eta_detection_eta_weight128_filtration_eleven
  from KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection
open private theta_square_detection_cases
  from KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
open private h6_square_dichotomy_realization_additive h6_square_dichotomy_realize_detector
  h6_square_dichotomy_high125_detector_nonzero_parts h6_square_dichotomy_theta_detector_zero_parts
  from KIP126.Main.SectionSeven.DifferentialCriterion.Dichotomy
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
  {η : BiHom 1 2 (S_0_0 : Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

include D in
private theorem lambda_eta_square_eq_multiply (θ : BiHom 62 64 (S_0_0 : Syn)) :
    lambdaEtaThetaSquare η θ = lambdaMultiply 1 (etaThetaSquare η θ) := by
  unfold lambdaEtaThetaSquare lambdaAction lambdaMultiply
  rw [lambdaPow_one D.shiftCoherence]
  rfl

/-- Remark 7.5: only the lambda-eta-square expression is asserted independent
of the admissible theta choice. Its higher-filtration error is killed by tmf. -/
theorem lambda_eta_theta_square_independent
    (A : AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (AF : SphereActionFiltrationCompatible D) (SF : Derived.SphereFacts I.interpretation)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toAdamsComparisonData θ)
    (hθ' : ThetaChoice M D.toAdamsComparisonData θ') :
    lambdaEtaThetaSquare η θ = lambdaEtaThetaSquare η θ' := by
  classical
  have hgap := theta_square_choice_theta_choice_filtration_gap_of_pages A.synthetic
    (theta_square_choice_theta_choice_finite_pages I) θ θ' hθ hθ'
  have hsquare : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12
      (sphereProduct θ θ - sphereProduct θ' θ') := by
    rw [theta_square_choice_theta_square_difference D θ θ'
      (theta_square_choice_theta_degree_order_two A.synthetic A.realization A.classical θ')]
    exact AF .sphere 62 64 62 64 6 6 (θ-θ') (θ-θ') hgap hgap
  have h13 := (theta_square_detection_cases I A.synthetic V SF).1
  have herror := eta_detection_eta_weight128_filtration_eleven I A.synthetic SF h13
    η A.classical.hopf.1 _
    (towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu)
      (S_0_0 : Syn) (124,128) (by decide : (11:ℤ) ≤ 12) hsquare)
  have hlinear : sphereProduct η (sphereProduct θ θ - sphereProduct θ' θ') =
      sphereProduct η (sphereProduct θ θ) - sphereProduct η (sphereProduct θ' θ') := by
    simp only [sphereProduct, Int.reduceAdd, Preadditive.comp_sub]
  rw [hlinear] at herror
  have detector_zero (a : BiHom 62 64 (S_0_0 : Syn))
      (ha : ThetaChoice M D.toAdamsComparisonData a) :
      sphereProduct η (sphereProduct a a) ≫ detectorMap D = 0 := by
    have h := h6_square_dichotomy_theta_detector_zero_parts A.synthetic A.realization
      A.classical A.tmf a ha
    dsimp only [sphereProduct]
    simp only [Smn] at h
    simp only [Smn, Category.assoc]
    rw [h]
    erw [comp_zero, comp_zero, comp_zero, comp_zero]
  let a : BiHom 125 130 (S_0_0 : Syn) :=
    sphereProduct η (sphereProduct θ θ) - sphereProduct η (sphereProduct θ' θ')
  have hz : a ≫ detectorMap D = 0 := by
    simp only [a, Preadditive.sub_comp, detector_zero θ hθ, detector_zero θ' hθ', sub_self]
  have heq : a = 0 := by
    letI := h6_square_dichotomy_realization_additive (D := D)
    by_contra hne
    have hd := high125_weight130_nonzero_classical_detection I A.synthetic A.realization V
      A.tmf.high125_detected.1 a herror hne
    have hn := h6_square_dichotomy_high125_detector_nonzero_parts A.tmf I V S
      (realizeNu D A.realization.coordinates .sphere (a ≫ D.nu.unitIso.inv)) hd
    apply hn
    rw [h6_square_dichotomy_realize_detector, hz]
    simp only [realizeNu, Functor.map_zero, comp_zero, zero_comp]
  exact congrArg (lambdaAction 125 130 (S_0_0 : Syn)) (sub_eq_zero.mp heq)

private theorem h6_square_basis (I : AdamsComputationTheorems D L G) :
    I.interpretation.basis .sphere 2 128 0 = Sphere.Internal.hiSquare H M 6 := by
  have label : I.interpretation.sphere 2 128 dataH6Sq =
      I.interpretation.basis .sphere 2 128 0 := by
    have hc := I.monomials (⟨.sphere,2,128,["69,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 100) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
    have heq : dataH6Sq=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ ^ 2 = projection (monomialOfString "69,2")
      have hs : "69,2"≠"" := by decide
      have hp : (("69,2".splitOn ",").map (fun n=>n.toNat?.getD 0))=[69,2] := by
        have split : "69,2".splitOn ","=["69","2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,map_pow,pow_two]
    rw [heq]
    exact he
  exact label.symm.trans I.distinguishedClasses.h6_square

/-- The zero endpoint follows from the finite E7 computation and the zero
incoming d2 source, independently of the final permanence theorem. -/
theorem h6_square_survives_three (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 3 (2,128) (Sphere.Internal.hiSquare H M 6) := by
  have hrow := I.adamsStatements
    ⟨.sphere,.reaches,7,2,128,[0],2,128,[],"S0_AdamsE2_ss",2314⟩
    (List.mem_of_getElem? (i := 146) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 128 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx, h6_square_basis I] at h
  obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ) ≤ 3) (by decide : (3:ℤ) ≤ 7) h
  refine ⟨a,ha,?_⟩
  apply represents_next_nonzero_of_incoming_zero (E := sequence D .sphere) (r := 2)
    (by change (2:ℤ) ≤ 2; omega) (by decide)
    (sphereAdamsInternal_h6_incoming_d_eq_zero H 2 (by decide))
    ha (represents_two_self _) ?_
  rw [← h6_square_basis I]
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,128,["69,2"]⟩
    (List.mem_of_getElem? (i := 100) (by rfl))
  change (sequence D .sphere).Page 2 (2,128) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 128 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 1) 1) =
      I.interpretation.basis .sphere 2 128 0 := he 0
  rw [← he0, LinearEquiv.map_ne_zero_iff]
  simp

include D in
private theorem lambda_eta_theta_square_mod_lambda_zero
    (θ : BiHom 62 64 (S_0_0 : Syn)) :
    VanishesModLambda 1 (lambdaEtaThetaSquare η θ) := by
  rw [lambda_eta_square_eq_multiply (D := D)]
  dsimp only [VanishesModLambda, quotientClass, lambdaMultiply]
  rw [Category.assoc, Category.assoc, ← lambdaPow_naturality]
  simp only [Category.assoc, XModLambdaN.lambdaPow_comp_incl, comp_zero]

/-- The finite normalized BX criterion for all natural r, including zero,
and the untruncated criterion, for every admissible theta choice. -/
theorem any_choice_criterion_all_r
    (A : AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (AF : SphereActionFiltrationCompatible D) (SF : Derived.SphereFacts I.interpretation)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hθ : ThetaChoice M D.toAdamsComparisonData θ) :
    (∀ r : ℕ, SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      ((r : ℤ)+3) (2,128) (Sphere.Internal.hiSquare H M 6) ↔
      VanishesModLambda (r+1) (lambdaEtaThetaSquare η θ)) ∧
    BJMUntruncatedCriterion H M η θ := by
  obtain ⟨θ',hsource,_,huntruncated⟩ := A.bx
  have he := lambda_eta_theta_square_independent A I AF SF V S θ θ' hθ hsource.2.1
  constructor
  · intro r
    cases r with
    | zero => exact ⟨fun _ => lambda_eta_theta_square_mod_lambda_zero (D := D) θ,
        fun _ => h6_square_survives_three I⟩
    | succ r =>
      rw [he, lambda_eta_square_eq_multiply (D := D)]
      exact (hsource.2.2.2 (r+1) (by omega)).trans
        (bx_finite_lambda_normalization A I (r+1) (by omega) (etaThetaSquare η θ'))
  · unfold BJMUntruncatedCriterion
    rw [he]
    exact huntruncated

/-- The original positive-r proposition now has a proof from the same inputs. -/
theorem any_choice_criterion_of_theorems
    (A : AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (AF : SphereActionFiltrationCompatible D) (SF : Derived.SphereFacts I.interpretation)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H) :
    any_choice_criterion M D η := by
  intro _ θ hθ
  obtain ⟨hfinite,huntruncated⟩ := any_choice_criterion_all_r A I AF SF V S θ hθ
  exact ⟨fun r _ => hfinite r, huntruncated⟩

end
end KIP126.Main.Stem126.BJMInduction
