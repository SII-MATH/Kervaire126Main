module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteMay3x3
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.MahowaldLeibniz.NativeImageSquare

/-! The actual first-quotient cofiber calculation associated to the numerical
nu extension.  The common representative is constructed in the selected
lambda cofiber, without replacing it by a tensor quotient.  All declarations
are private; neither the desired cofiber differential nor an arbitrary
source with the same degree is introduced as an assumption. -/

@[expose] section
namespace KIP126.ProofTools.Paper.NuCofiberNumericalDifferential
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Leibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

private abbrev nuTriangle :=
  normalizedTriangle model model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum

private def nuTopIso : nuTriangle.obj₁⟦(1 : ℤ)⟧ ≅
    model.nu.functor.obj ((ClassicalObject.shift 1 (.shift 3 .sphere)).obj
      model.auxiliary) :=
  normalizedSuspensionNativeIso model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum
    KIP126.Literature.Standard.nuCofiber_nu_exponent

private def nuCofiberIso : nuTriangle.obj₃ ≅
    model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) :=
  normalizedThirdZeroIso model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum
    KIP126.Literature.Standard.nuCofiber_bottom_exponent

private theorem native_first_label_surjective (X : ClassicalObject) (s t : ℤ) :
    Function.Surjective (nativeFirstLabel X s t) := by
  intro a
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨x, hx⟩ := firstLabel_surjective X s t
    (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app V) 1)
  refine ⟨x, ?_⟩
  unfold nativeFirstLabel
  rw [hx, Category.assoc, ← model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app, model.quotients.functoriality.map_id]
  simp only [Functor.id_obj, V, Category.comp_id]

private theorem native_first_label_sub (X : ClassicalObject) (s t : ℤ)
    (x y : Ambient model X (s,t)) :
    nativeFirstLabel X s t (x-y) = nativeFirstLabel X s t x - nativeFirstLabel X s t y := by
  unfold nativeFirstLabel
  rw [firstLabel_sub, Preadditive.sub_comp]

private theorem native_first_label_zero (X : ClassicalObject) (s t : ℤ) :
    nativeFirstLabel X s t 0 = 0 := by
  have h := native_first_label_sub X s t 0 0
  simpa only [sub_self] using h

private theorem native_first_label_neg (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) :
    nativeFirstLabel X s t (-x) = -(nativeFirstLabel X s t x) := by
  simpa only [zero_sub, native_first_label_zero] using
    native_first_label_sub X s t 0 x

private theorem native_first_label_injective (X : ClassicalObject) (s t : ℤ) :
    Function.Injective (nativeFirstLabel X s t) := by
  intro x y hxy
  have h : nativeFirstLabel X s t (x-y) = 0 := by
    rw [native_first_label_sub, hxy, sub_self]
  exact sub_eq_zero.mp (first_label_zero X s t (x-y) h)

private theorem bi_suspension_boundary_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B)
    (a : BiHom 34 37
      (((SyntheticCategory.biShift (0, -1)).obj A)⟦(1 : ℤ)⟧)) :
    biSuspensionHomEquiv 34 37 1 B
      (a ≫ (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -1)).map f)) =
      biSuspensionHomEquiv 34 37 1 A a ≫ f :=
  bi_susp_natural model.quotients.coherence 34 37 1 f a

/-- The correction produced by TR4 is zero on the actual sphere group.
The source and target shifts are retained, rather than discarded by an
object-only cofiber comparison. -/
private theorem nu_lambda_restriction_no_return (m w : ℤ)
    (b : BiHom m w
      (((SyntheticCategory.biShift (0, -1)).obj nuTriangle.obj₂)⟦(1 : ℤ)⟧))
    (z : ((SyntheticCategory.biShift (0, -1)).obj nuTriangle.obj₂)⟦(1 : ℤ)⟧ ⟶
      XModLambdaN (nuTriangle.obj₁⟦(1 : ℤ)⟧) 1) : b ≫ z = 0 := by
  let eS : ((SyntheticCategory.biShift (0, -1)).obj nuTriangle.obj₂)⟦(1 : ℤ)⟧ ≅
      (SyntheticCategory.biShift (1, -1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    (biSuspensionIso 1 nuTriangle.obj₂).symm
  let eQ := (model.quotients.functoriality.functor 1).mapIso nuTopIso
  have hz := shifted_nu_to_shifted_finite_no_return
    .sphere (.shift 1 (.shift 3 .sphere)) 1 (by decide)
    (1, -1) (0, 0) (by norm_num) m w (b ≫ eS.hom)
    (eS.inv ≫ z ≫ eQ.hom ≫ SyntheticCategory.biShift_zero.inv.app _)
  have hz' : (b ≫ z) ≫ eQ.hom ≫ SyntheticCategory.biShift_zero.inv.app _ = 0 := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz
  apply (cancel_mono (eQ.hom ≫ SyntheticCategory.biShift_zero.inv.app _)).mp
  simpa only [Category.assoc, zero_comp] using hz'

/-- A pair satisfying the full normalized nu square gives one actual
first-quotient cofiber representative with both prescribed images.
The hypotheses are the exact full representative equation; they are
discharged by the independent numerical nu construction. -/
private theorem nu_lambda_common_lift (m w : ℤ)
    (a : BiHom m w (nuTriangle.obj₁⟦(1 : ℤ)⟧))
    (b : BiHom m w
      (((SyntheticCategory.biShift (0, -1)).obj nuTriangle.obj₂)⟦(1 : ℤ)⟧))
    (hab : a ≫ (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map nuTriangle.mor₁)) =
      b ≫ (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
        (lambdaPow 1 nuTriangle.obj₂)) :
    ∃ c : BiHom m w (XModLambdaN nuTriangle.obj₃ 1),
      c ≫ XModLambdaN.map nuTriangle.mor₃ 1 =
        a ≫ XModLambdaN.incl (nuTriangle.obj₁⟦(1 : ℤ)⟧) 1 ∧
      c ≫ XModLambdaN.proj nuTriangle.obj₃ 1 =
        b ≫ (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -1)).map nuTriangle.mor₂) := by
  letI := model.exactness.syntheticTriangulated
  exact ThreeByThree.common_lift_of_no_return
    (lambdaPow 1 nuTriangle.obj₂) nuTriangle.mor₂
    ((SyntheticCategory.biShift (0, -1)).map nuTriangle.mor₂)
    (lambdaPow 1 nuTriangle.obj₃) (XModLambdaN.incl nuTriangle.obj₃ 1)
    (XModLambdaN.proj nuTriangle.obj₃ 1)
    nuTriangle.mor₃ (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map nuTriangle.mor₁))
    (XModLambdaN.incl (nuTriangle.obj₁⟦(1 : ℤ)⟧) 1)
    (XModLambdaN.map nuTriangle.mor₃ 1)
    (rot_of_distTriang _ KIP126.Literature.Standard.nuCofiber_distinguished)
    (XModLambdaN.cofiberTriangle_distinguished _ 1)
    (lambdaPow_naturality 1 nuTriangle.mor₂)
    (XModLambdaN.incl_naturality nuTriangle.mor₃ 1).symm
    (nu_lambda_restriction_no_return m w) a b hab

private def bottomH0P : Ambient model .nuCofiber (5,38) :=
  (model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38)
    NumericalExamples.h0p

/-- Decode the same constructed cofiber representative, retaining both
actual cell labels.  The suspended input is the actual full normalized-nu
square; no cofiber differential is assumed. -/
private theorem nu_cofiber_d2_of_suspended_pair
    (a : BiHom 34 37 (nuTriangle.obj₁⟦(1 : ℤ)⟧))
    (β : BiHom 33 38 nuTriangle.obj₂)
    (uTop : Ambient model (.shift 1 (.shift 3 .sphere)) (3,37))
    (haTop : a ≫ XModLambdaN.incl (nuTriangle.obj₁⟦(1 : ℤ)⟧) 1 ≫
      XModLambdaN.map nuTopIso.hom 1 =
        nativeFirstLabel (.shift 1 (.shift 3 .sphere)) 3 37 uTop)
    (hβ : β ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel .sphere 5 38 NumericalExamples.h0p)
    (hab : a ≫ (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map nuTriangle.mor₁)) =
      (-(biSuspensionHomEquiv 34 37 1 nuTriangle.obj₂).symm β) ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (lambdaPow 1 nuTriangle.obj₂)) :
    ∃ xbar : Ambient model .nuCofiber (3,37),
      (model.classical.map model.auxiliary.nuRouteTriangle.h).pageMap 2 (3,37) xbar = uTop ∧
      DifferentialAt model .nuCofiber 2 (3,37) (5,38) xbar bottomH0P ∧
      IsPermanent model .nuCofiber (5,38) bottomH0P := by
  obtain ⟨c, hcTop, hcBoundary⟩ := nu_lambda_common_lift 34 37 a
    (-(biSuspensionHomEquiv 34 37 1 nuTriangle.obj₂).symm β) hab
  let cNative := c ≫ XModLambdaN.map nuCofiberIso.hom 1
  obtain ⟨xbar, hxbar⟩ := native_first_label_surjective .nuCofiber 3 37 cNative
  have hbottom : (β ≫ nuTriangle.mor₂ ≫ nuCofiberIso.hom) ≫
      XModLambdaN.incl _ 1 = nativeFirstLabel .nuCofiber 5 38 bottomH0P := by
    have hG := normalized_second_arrow_zero
      model.auxiliary.nuRouteTriangle KIP126.Literature.Standard.nuCofiber_exponent_sum
      KIP126.Literature.Standard.nuCofiber_bottom_exponent
    change nuTriangle.mor₂ ≫ nuCofiberIso.hom =
      model.nu.functor.map model.auxiliary.nuRouteTriangle.g at hG
    rw [hG]
    rw [Category.assoc, XModLambdaN.incl_naturality, ← Category.assoc, hβ]
    exact native_first_label_natural .sphere .nuCofiber
      model.auxiliary.nuRouteTriangle.g 5 38 NumericalExamples.h0p
  have hcEval : biSuspensionHomEquiv 34 37 1 nuTriangle.obj₃
      (c ≫ XModLambdaN.proj _ 1) = -(β ≫ nuTriangle.mor₂) := by
    rw [hcBoundary, Preadditive.neg_comp, map_neg,
      bi_suspension_boundary_natural, AddEquiv.apply_symm_apply]
  have hcNativeEval : biSuspensionHomEquiv 34 37 1
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))
      (cNative ≫ XModLambdaN.proj _ 1) =
        -(β ≫ nuTriangle.mor₂ ≫ nuCofiberIso.hom) := by
    dsimp only [cNative]
    rw [Category.assoc, XModLambdaN.proj_naturality, ← Category.assoc]
    change biSuspensionHomEquiv 34 37 1 _
      ((c ≫ XModLambdaN.proj _ 1) ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map
          ((SyntheticCategory.biShift (0,-1)).map nuCofiberIso.hom)) = _
    rw [bi_suspension_boundary_natural, hcEval, Preadditive.neg_comp, Category.assoc]
  have hlabel : adjacentBoundaryLabel .nuCofiber 1 3 37 cNative =
      nativeFirstLabel .nuCofiber 5 38 bottomH0P := by
    change (biSuspensionHomEquiv 34 37 1
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))
      (cNative ≫ XModLambdaN.proj _ 1)) ≫ XModLambdaN.incl _ 1 = _
    rw [hcNativeEval, Preadditive.neg_comp, hbottom]
    have hn : -bottomH0P = bottomH0P := neg_eq_of_add_eq_zero_left
      (classical_page_two (ClassicalObject.nuCofiber.obj model.auxiliary) 2 (5,38) bottomH0P)
    rw [← native_first_label_neg, hn]
  refine ⟨xbar, ?_, ?_, ?_⟩
  · apply native_first_label_injective (.shift 1 (.shift 3 .sphere)) 3 37
    have hq := native_first_label_natural .nuCofiber (.shift 1 (.shift 3 .sphere))
      model.auxiliary.nuRouteTriangle.h 3 37 xbar
    change nativeFirstLabel .nuCofiber 3 37 xbar ≫
      XModLambdaN.map (model.nu.functor.map model.auxiliary.nuRouteTriangle.h) 1 = _ at hq
    refine hq.symm.trans ?_
    rw [hxbar]
    dsimp only [cNative]
    have hH := normalized_third_arrow_zero model.auxiliary.nuRouteTriangle
      KIP126.Literature.Standard.nuCofiber_exponent_sum
      KIP126.Literature.Standard.nuCofiber_nu_exponent
      KIP126.Literature.Standard.nuCofiber_bottom_exponent
      KIP126.Literature.Standard.nuCofiber_top_exponent
    change nuTriangle.mor₃ ≫ nuTopIso.hom =
      nuCofiberIso.hom ≫ model.nu.functor.map model.auxiliary.nuRouteTriangle.h at hH
    rw [Category.assoc, ← model.quotients.functoriality.map_comp, ← hH,
      model.quotients.functoriality.map_comp, ← Category.assoc, hcTop]
    simpa only [Category.assoc] using haTop
  · refine ⟨by decide, ?_⟩
    apply (differential_iff_specified_adjacent_lift .nuCofiber 1 (by decide)
      3 37 xbar bottomH0P).mpr
    refine ⟨cNative, ?_, hlabel⟩
    simpa only [(model.quotients.tower _).rho_id, Category.comp_id] using hxbar.symm
  · exact first_label_lift_permanent .nuCofiber 5 38 bottomH0P
      (β ≫ nuTriangle.mor₂ ≫ nuCofiberIso.hom) hbottom


/-- Ordinary suspension of a full map, with its zero vertical shift
removed by the specified unit comparison. -/
private def ordinarySuspend {A : SyntheticSpectrum} (a : BiHom 33 37 A) :
    BiHom 34 37 (A⟦(1:ℤ)⟧) :=
  (biSuspensionHomEquiv 34 37 0 A).symm a ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (SyntheticCategory.biShift_zero.hom.app A)

private theorem ordinary_suspend_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (a : BiHom 33 37 A) :
    ordinarySuspend a ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f =
      ordinarySuspend (a ≫ f) := by
  unfold ordinarySuspend
  have hzNat : SyntheticCategory.biShift_zero.hom.app A ≫ f =
      (SyntheticCategory.biShift (0,0)).map f ≫
        SyntheticCategory.biShift_zero.hom.app B :=
    (SyntheticCategory.biShift_zero.hom.naturality f).symm
  rw [Category.assoc,←Functor.map_comp,hzNat,Functor.map_comp,←Category.assoc]
  congr 1
  apply (biSuspensionHomEquiv 34 37 0 B).injective
  calc
    _ = biSuspensionHomEquiv 34 37 0 A
        ((biSuspensionHomEquiv 34 37 0 A).symm a) ≫ f :=
      bi_susp_natural model.quotients.coherence 34 37 0 f _
    _ = _ := by rw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]

private theorem ordinary_suspend_lambda (B : SyntheticSpectrum)
    (β : BiHom 33 38 B) :
    ordinarySuspend (lambdaMultiply 1 β) =
      (biSuspensionHomEquiv 34 37 1 B).symm β ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow 1 B) := by
  have hl := lambdaRestrictionSourceMap_commutes model.quotients.coherence 0 1
    (by decide) B
  have hz : lambdaPow 0 B = SyntheticCategory.biShift_zero.hom.app B := by
    rfl
  rw [hz] at hl
  unfold ordinarySuspend
  rw [←hl,Functor.map_comp,←Category.assoc]
  congr 1
  apply (biSuspensionHomEquiv 34 37 0 B).injective
  rw [AddEquiv.apply_symm_apply]
  exact (bi_susp_lambda_transition model.quotients.coherence 0 1
    (by decide) 34 37 B β).symm

private theorem suspended_full_pair_square
    (a : BiHom 33 37 nuTriangle.obj₁)
    (β : BiHom 33 38 nuTriangle.obj₂)
    (hab : a ≫ nuTriangle.mor₁ = lambdaMultiply 1 β) :
    ordinarySuspend a ≫ (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map nuTriangle.mor₁)) =
      (-(biSuspensionHomEquiv 34 37 1 nuTriangle.obj₂).symm β) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow 1 nuTriangle.obj₂) := by
  rw [Preadditive.comp_neg,Preadditive.neg_comp,
    ordinary_suspend_natural,hab,ordinary_suspend_lambda]


private def nuPositiveSourceIso : nuTriangle.obj₁ ≅
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) :=
  normalizedPositiveSourceIso model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_nu_exponent

private theorem nu_positive_source_map :
    nuPositiveSourceIso.inv ≫ nuTriangle.mor₁ =
      NuNumericalExtensions.positiveNuNormalizedMap := by
  have h := normalizedPositiveSourceIso_map model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_nu_exponent
  change nuPositiveSourceIso.hom ≫ NuNumericalExtensions.positiveNuNormalizedMap =
    nuTriangle.mor₁ at h
  rw [←h,Iso.inv_hom_id_assoc]


private theorem ordinarySuspend_same_first {A : SyntheticSpectrum}
    (a b : BiHom 33 37 A)
    (hab : a≫XModLambdaN.incl A 1=b≫XModLambdaN.incl A 1) :
    ordinarySuspend a≫XModLambdaN.incl (A⟦(1:ℤ)⟧) 1=
      ordinarySuspend b≫XModLambdaN.incl (A⟦(1:ℤ)⟧) 1 := by
  obtain ⟨ε,hε⟩ := quotient_suspension_inclusion_exists A 1
  apply (cancel_mono ε.hom).mp
  rw [Category.assoc,Category.assoc,hε,ordinary_suspend_natural,
    ordinary_suspend_natural,hab]

private theorem permanent_native_full_lift (X : ClassicalObject)
    (x : Ambient model X (3,36))
    (hx : x∈permanentCycles model X (3,36)) :
    ∃ b : BiHom 33 36 (model.nu.functor.obj (X.obj model.auxiliary)),
      b≫XModLambdaN.incl _ 1=nativeFirstLabel X 3 36 x := by
  have hp := NuNumericalExtensions.permanent_cycle_of_member X (3,36) x hx
  obtain ⟨b,hb⟩ := (KIP126.Literature.Standard.selected_permanent_lift X 3 36 x).mp hp
  refine ⟨b≫SyntheticCategory.biShift_zero.hom.app _,?_⟩
  unfold nativeFirstLabel
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
  exact congrArg (fun z => z≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hb

private def ordinaryNatIso :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,0) ≅
      shiftFunctor SyntheticSpectrum (1:ℤ) :=
  boundarySuspensionNatIso 0 ≪≫
    Functor.isoWhiskerRight SyntheticCategory.biShift_zero (shiftFunctor SyntheticSpectrum (1:ℤ)) ≪≫
    Functor.leftUnitor _

private def positiveSuspensionComparison :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1) ⋙
      SyntheticCategory.biShift (1,0) ≅ SyntheticCategory.biShift (1,1) :=
  Functor.isoWhiskerLeft _ ordinaryNatIso ≪≫ positiveOrdinaryIso

private theorem ordinary_positive_source_geometry
    (A : SyntheticSpectrum) (b : BiHom 33 36 A) :
    ∃ σ : Smn (Syn:=SyntheticSpectrum) 34 37 ≅ Smn 34 37,
      ordinarySuspend (shiftHomotopyClass (0,1) (33,36) b) ≫
          positiveOrdinaryIso.hom.app A =
        σ.hom ≫ shiftHomotopyClass (1,1) (33,36) b := by
  let L : Smn (Syn:=SyntheticSpectrum) 34 37 ≅
      (SyntheticCategory.biShift (1,0)).obj
        ((SyntheticCategory.biShift (0,1)).obj (Smn (Syn:=SyntheticSpectrum) 33 36)) :=
    ((SyntheticCategory.biShift_comp (33,37) (1,0)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift (1,0)).mapIso
        ((SyntheticCategory.biShift_comp (33,36) (0,1)).app S_0_0).symm
  let R : Smn (Syn:=SyntheticSpectrum) 34 37 ≅
      (SyntheticCategory.biShift (1,1)).obj (Smn (Syn:=SyntheticSpectrum) 33 36) :=
    ((SyntheticCategory.biShift_comp (33,36) (1,1)).app S_0_0).symm
  let σ := L ≪≫ positiveSuspensionComparison.app (Smn (Syn:=SyntheticSpectrum) 33 36) ≪≫ R.symm
  refine ⟨σ,?_⟩
  have hn := positiveSuspensionComparison.hom.naturality b
  have hraw : ordinarySuspend (shiftHomotopyClass (0,1) (33,36) b) ≫
      positiveOrdinaryIso.hom.app A =
      L.hom ≫ (SyntheticCategory.biShift (0,1) ⋙ SyntheticCategory.biShift (1,0)).map b ≫
        positiveSuspensionComparison.hom.app A := by
    rw [ordinarySuspend,bi_susp_symm_eq]
    simp [L,positiveSuspensionComparison,ordinaryNatIso,boundarySuspensionNatIso,
      shiftHomotopyClass,susp_invariance,homotopyRegrade,Iso.homCongr,Category.assoc]
  rw [hraw,hn]
  simp [σ,R,shiftHomotopyClass,Category.assoc]


private theorem positive_source_native_suspension_compare
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=1) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).inv ≫
        (normalizedSuspensionNativeIso T he hf).hom =
      positiveOrdinaryIso.hom.app (model.nu.functor.obj (T.X.obj model.auxiliary)) ≫
        (model.nu.suspensionIso (T.X.obj model.auxiliary)).inv := by
  have h := normalizedPositiveSourceIso_suspension T he hf
  have H := congrArg (fun z =>
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).inv ≫ z ≫
      (model.nu.suspensionIso (T.X.obj model.auxiliary)).inv) h
  have hm : (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom = 𝟙 _ := by
    rw [←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at H
  simpa only [←Category.assoc,hm,Category.id_comp] using H.symm

private theorem positive_ordinary_suspend_native_first
    (X : ClassicalObject) (x : Ambient model X (3,36))
    (hx : x∈permanentCycles model X (3,36))
    (a : BiHom 33 37 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (ha : a≫XModLambdaN.incl _ 1=(model.firstQuotient X 1 3 36).symm x) :
    ∃ sx : Ambient model (.shift 1 X) (3,37),
      (model.classicalSuspension X).DesuspendsClass 3 37 sx x ∧
      ordinarySuspend a≫XModLambdaN.incl _ 1≫
        XModLambdaN.map (positiveOrdinaryIso.hom.app
          (model.nu.functor.obj (X.obj model.auxiliary)) ≫
            (model.nu.suspensionIso (X.obj model.auxiliary)).inv) 1 =
          nativeFirstLabel (.shift 1 X) 3 37 sx := by
  obtain ⟨b,hb⟩ := permanent_native_full_lift X x hx
  obtain ⟨sx,hsx,hsb⟩ := NuNumericalExtensions.exists_suspend_nu_first_label X 3 36 x b hb
  refine ⟨sx,hsx,?_⟩
  have hpos := NuNumericalExtensions.positive_shift_full_first_label X 3 36 x b hb
  have haq : a≫XModLambdaN.incl _ 1=
      shiftHomotopyClass (0,1) (33,36) b≫XModLambdaN.incl _ 1 := by
    exact ha.trans hpos.symm
  let E : ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧ ⟶
        model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary) :=
    positiveOrdinaryIso.hom.app (model.nu.functor.obj (X.obj model.auxiliary)) ≫
      (model.nu.suspensionIso (X.obj model.auxiliary)).inv
  change ordinarySuspend a≫XModLambdaN.incl _ 1≫XModLambdaN.map E 1 = _
  rw [←Category.assoc,ordinarySuspend_same_first a _ haq]
  rw [Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc]
  obtain ⟨σ,hσ⟩ := ordinary_positive_source_geometry _ b
  change (ordinarySuspend (shiftHomotopyClass (0,1) (33,36) b)≫
    positiveOrdinaryIso.hom.app _≫(model.nu.suspensionIso (X.obj model.auxiliary)).inv)≫
      XModLambdaN.incl _ 1 = _
  rw [←Category.assoc _ (positiveOrdinaryIso.hom.app _),hσ,Category.assoc]
  have hproj := sphere_automorphism_quotient_projection 34 37 σ
    (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary))
      (shiftHomotopyClass (1,1) (33,36) b≫
        (model.nu.suspensionIso (X.obj model.auxiliary)).inv)
  calc
    _ = (shiftHomotopyClass (1,1) (33,36) b≫
        (model.nu.suspensionIso (X.obj model.auxiliary)).inv)≫XModLambdaN.incl _ 1 := by
      simpa only [Category.assoc,ClassicalObject.obj,Prod.mk_add_mk,Prod.fst,Prod.snd,Int.reduceAdd] using hproj
    _ = _ := hsb


private theorem suspended_nu_source_label
    (x : Ambient model (.shift 3 .sphere) (3,36))
    (hx : x ∈ permanentCycles model (.shift 3 .sphere) (3,36))
    (a : BiHom 33 37 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))))
    (ha : a ≫ XModLambdaN.incl _ 1 =
      (model.firstQuotient (.shift 3 .sphere) 1 3 36).symm x) :
    ∃ sx : Ambient model (.shift 1 (.shift 3 .sphere)) (3,37),
      (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 3 37 sx x ∧
      ordinarySuspend (a ≫ nuPositiveSourceIso.inv) ≫
        XModLambdaN.incl (nuTriangle.obj₁⟦(1:ℤ)⟧) 1 ≫
          XModLambdaN.map nuTopIso.hom 1 =
            nativeFirstLabel (.shift 1 (.shift 3 .sphere)) 3 37 sx := by
  obtain ⟨sx,hsx,hs⟩ := positive_ordinary_suspend_native_first
    (.shift 3 .sphere) x hx a ha
  refine ⟨sx,hsx,?_⟩
  have hcomp := positive_source_native_suspension_compare
    model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum
    KIP126.Literature.Standard.nuCofiber_nu_exponent
  change (shiftFunctor SyntheticSpectrum (1:ℤ)).map nuPositiveSourceIso.inv ≫
    nuTopIso.hom = _ at hcomp
  rw [←ordinary_suspend_natural]
  have hi := XModLambdaN.incl_naturality
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map nuPositiveSourceIso.inv) 1
  have heq := congrArg (fun z => ordinarySuspend a ≫ z ≫
    XModLambdaN.map nuTopIso.hom 1) hi
  simp only [Category.assoc] at heq ⊢
  refine heq.trans ?_
  rw [←model.quotients.functoriality.map_comp,hcomp]
  exact hs

/-- The actual cofiber d₂, with both fixed cell maps and the actual
suspension of the archived h₀h₄² source.  Every representative premise
of the intermediate TR4 calculation is supplied by the independent
full numerical nu construction. -/
private theorem paper6_19_actual_cofiber_d2 :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      NumericalExamples.IsSphereThreeH0H4Square x ∧
      x ∈ permanentCycles model (.shift 3 .sphere) (3,36) ∧
      ∃ uTop : Ambient model (.shift 1 (.shift 3 .sphere)) (3,37),
        (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 3 37 uTop x ∧
        ∃ xbar : Ambient model .nuCofiber (3,37),
          (model.classical.map model.auxiliary.nuRouteTriangle.h).pageMap 2 (3,37) xbar = uTop ∧
          DifferentialAt model .nuCofiber 2 (3,37) (5,38) xbar bottomH0P ∧
          IsPermanent model .nuCofiber (5,38) bottomH0P := by
  obtain ⟨x,hx,hxp,a,β,ha,hβ,hab⟩ :=
    NuNumericalExtensions.paper6_24_full_nu_representatives
  obtain ⟨uTop,huTop,haTop⟩ := suspended_nu_source_label x hxp a ha
  have hfull : (a ≫ nuPositiveSourceIso.inv) ≫ nuTriangle.mor₁ =
      lambdaMultiply 1 β := by
    rw [Category.assoc,nu_positive_source_map]
    exact hab
  obtain ⟨xbar,hTop,hDiff,hPerm⟩ := nu_cofiber_d2_of_suspended_pair
    (ordinarySuspend (a ≫ nuPositiveSourceIso.inv)) β uTop haTop hβ
      (suspended_full_pair_square (a ≫ nuPositiveSourceIso.inv) β hfull)
  exact ⟨x,hx,hxp,uTop,huTop,xbar,hTop,hDiff,hPerm⟩

end
end KIP126.ProofTools.Paper.NuCofiberNumericalDifferential
end
