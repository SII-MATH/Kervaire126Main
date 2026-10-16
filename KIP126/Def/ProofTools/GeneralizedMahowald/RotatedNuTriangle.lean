module
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import KIP126.Def.Literature.Standard

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
set_option Elab.async false

private def rotatedNuRouteTriangle : TriangleData model.auxiliary where
  X := .sphere
  Y := .nuCofiber
  Z := .shift 1 (.shift 3 .sphere)
  f := model.auxiliary.nuRouteTriangle.g
  g := model.auxiliary.nuRouteTriangle.h
  h := -((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap)
  distinguished := rot_of_distTriang _ model.auxiliary.nuRouteTriangle.distinguished

private theorem rotated_nu_f_exponent :
    normalizedExponent model.classicalTower rotatedNuRouteTriangle.f = 0 :=
  KIP126.Literature.Standard.nuCofiber_bottom_exponent

private theorem rotated_nu_g_exponent :
    normalizedExponent model.classicalTower rotatedNuRouteTriangle.g = 0 :=
  KIP126.Literature.Standard.nuCofiber_top_exponent

private theorem suspension_projection_one (Y : ClassicalObject) :
    ((model.classicalSuspension Y).tower 1).hom ≫
        (shiftFunctor Spectrum (1:ℤ)).map
          ((model.classicalTower.tower (Y.obj model.auxiliary)).projection 1) =
      (model.classicalTower.tower ((ClassicalObject.shift 1 Y).obj model.auxiliary)).projection 1 := by
  have hcomm := (model.classicalSuspension Y).tower_comm 0 1 (by omega)
  have hzero := (model.classicalSuspension Y).tower_zero
  dsimp only [AbstractAdamsTower.projection,AbstractAdamsTower.mapAt,
    ClassicalObject.obj,Int.toNat_one,Int.toNat_zero] at *
  rw [Functor.map_comp,←Category.assoc,hcomm,Category.assoc,hzero]

private theorem map_filtration_one_shift_iff (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    MapFiltrationAtLeast model.classicalTower ((shiftFunctor Spectrum (1:ℤ)).map f) 1 ↔
      MapFiltrationAtLeast model.classicalTower f 1 := by
  let S := model.classicalSuspension Y
  let ff := Functor.FullyFaithful.ofFullyFaithful (shiftFunctor Spectrum (1:ℤ))
  constructor
  · rintro ⟨a,ha⟩
    let b := ff.preimage (a≫(S.tower 1).hom)
    refine ⟨b,?_⟩
    apply ff.map_injective
    change (shiftFunctor Spectrum (1:ℤ)).map (b≫_) = _
    rw [Functor.map_comp]
    dsimp only [b]
    rw [Functor.FullyFaithful.map_preimage,Category.assoc]
    erw [suspension_projection_one Y]
    exact ha
  · rintro ⟨a,ha⟩
    refine ⟨(shiftFunctor Spectrum (1:ℤ)).map a≫(S.tower 1).inv,?_⟩
    rw [Category.assoc]
    erw [←suspension_projection_one Y]
    simp only [S,Iso.inv_hom_id_assoc]
    rw [←Functor.map_comp]
    exact congrArg (shiftFunctor Spectrum (1:ℤ)).map ha

private theorem map_filtration_one_neg_iff {X Y : Spectrum} (f : X ⟶ Y) :
    MapFiltrationAtLeast model.classicalTower (-f) 1 ↔
      MapFiltrationAtLeast model.classicalTower f 1 := by
  constructor <;> rintro ⟨a,ha⟩ <;> refine ⟨-a,?_⟩
  · rw [Preadditive.neg_comp,ha,neg_neg]
  · rw [Preadditive.neg_comp,ha]

private theorem normalized_exponent_neg_shift (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    normalizedExponent model.classicalTower (-((shiftFunctor Spectrum (1:ℤ)).map f)) =
      normalizedExponent model.classicalTower f := by
  classical
  unfold normalizedExponent
  rw [map_filtration_one_neg_iff,map_filtration_one_shift_iff]

private theorem rotated_nu_h_exponent :
    normalizedExponent model.classicalTower rotatedNuRouteTriangle.h = 1 := by
  change normalizedExponent model.classicalTower (-((shiftFunctor Spectrum (1:ℤ)).map
    model.auxiliary.nuMap)) = 1
  rw [normalized_exponent_neg_shift (.shift 3 .sphere) .sphere,
    KIP126.Literature.Standard.nuCofiber_nu_exponent]

private theorem rotated_nu_exponent_sum :
    (normalizedExponent model.classicalTower rotatedNuRouteTriangle.f : ℤ) +
      normalizedExponent model.classicalTower rotatedNuRouteTriangle.g +
      normalizedExponent model.classicalTower rotatedNuRouteTriangle.h = 1 := by
  rw [rotated_nu_f_exponent,rotated_nu_g_exponent,rotated_nu_h_exponent]
  norm_num

/- The original selected normalized triangle rotates directly. The separate
selected triangle of the rotated classical data is proved distinguished below
using actual lambda-division uniqueness. -/
private theorem original_normalized_nu_rotation_distinguished :
    (KIP126.Literature.normalizedTriangle model model.auxiliary.nuRouteTriangle
      KIP126.Literature.Standard.nuCofiber_exponent_sum).rotate ∈ distTriang SyntheticSpectrum :=
  rot_of_distTriang _ KIP126.Literature.Standard.nuCofiber_distinguished

private theorem quotient_one_negative (X : ClassicalObject) (m w : ℤ)
    (h : w < m)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    a = 0 := by
  let e := (model.quotients.functoriality.functor 1).mapIso
    ((SyntheticCategory.biShift_zero (Syn:=SyntheticSpectrum)).symm.app
      (model.nu.functor.obj (X.obj model.auxiliary)))
  haveI := classical_page_negative X 2 (w-m) w (by omega)
  have he : a ≫ e.hom = 0 := by
    let e0 := model.firstQuotient X 0 (w-m) w
    have hz : (e0 (homotopyRegrade (by omega) (by simp) (a≫e.hom))) = 0 :=
      Subsingleton.elim _ _
    have hz' : homotopyRegrade (m':=w-(w-m)) (w':=w+0) (by omega) (by simp) (a≫e.hom) = 0 :=
      e0.injective (hz.trans (map_zero e0).symm)
    have hc {m' w' : ℤ} (hm : m=m') (hw : w=w')
        (c : BiHom m w (XModLambdaN (nuZero model X) 1)) :
        homotopyRegrade hm hw c=0 ↔ c=0 := by
      subst m'; subst w'; rfl
    exact (hc _ _ _).mp hz'

  exact (cancel_mono e.hom).mp (by simpa only [zero_comp] using he)

private theorem lambda_one_injective_of_quotient_vanishing
    (D Y : SyntheticSpectrum)
    (hz : ∀ b : D⟦(1:ℤ)⟧ ⟶ XModLambdaN Y 1, b=0)
    (a : D ⟶ (SyntheticCategory.biShift (0,-1)).obj Y)
    (ha : a≫SyntheticCategory.lam.app Y=0) : a=0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a≫F.map (lambdaPow 1 Y)=0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  have hf : F.map a=0 := by rw [hb,hz b,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

private theorem lambda_one_injective_at_diagonal (X : ClassicalObject) (m w : ℤ)
    (h : w ≤ m)
    (a : Smn (Syn:=SyntheticSpectrum) m w ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a≫SyntheticCategory.lam.app _ = 0) : a = 0 := by
  let Y := model.nu.functor.obj (X.obj model.auxiliary)
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a ≫ F.map (lambdaPow 1 Y) = 0 := by
    rw [←Functor.map_comp]
    have hpow : lambdaPow 1 Y = SyntheticCategory.lam.app Y :=
      lambdaPow_one model.quotients.coherence Y
    rw [hpow,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  have hz : eS.hom≫b=0 := quotient_one_negative X (m+1) w (by omega) _
  have hb0 : b=0 := (cancel_epi eS.hom).mp (by simpa only [comp_zero] using hz)
  have hf : F.map a=0 := by rw [hb,hb0,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

private theorem negative_lift_factorization {A B : SyntheticSpectrum} (k : ℕ)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    negativeLift k f ≫ lambdaPow k B = lambdaToPositivePow k A ≫ f := by
  simp only [negativeLift,lambdaToPositivePow,Category.assoc]
  rw [lambdaPow_naturality]

private theorem lambda_to_positive_zero (A : SyntheticSpectrum) :
    lambdaToPositivePow 0 A = SyntheticCategory.biShift_zero.inv.app A := by
  have hu := model.quotients.coherence.right_unit (0,0) A
  dsimp only [biShiftAddIso] at hu
  simp only [eqToIso_refl,Iso.trans_refl] at hu
  unfold lambdaToPositivePow
  norm_num only
  simp only [eqToHom_refl,Category.id_comp]
  change SyntheticCategory.biShift_zero.inv.app A ≫
    ((SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A)) = _
  erw [←hu,Iso.inv_hom_id_app,Category.comp_id]

private theorem normalized_zero_map_form {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k=0) (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hfg : lambdaToPositivePow k A≫f=g) :
    f = eqToHom (congrArg (fun j : ℕ =>
      (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≫
        SyntheticCategory.biShift_zero.hom.app A ≫ g := by
  subst k
  rw [lambda_to_positive_zero] at hfg
  have h := congrArg (fun z => SyntheticCategory.biShift_zero.hom.app A ≫ z) hfg
  erw [←Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at h
  simpa only [eqToHom_refl,Category.id_comp] using h

private theorem normalized_zero_map (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (he : normalizedExponent model.classicalTower f = 0) :
    (model.normalizedMap X Y f).map =
      eqToHom (congrArg (fun k : ℕ =>
        (SyntheticCategory.biShift (0,(k:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) he) ≫
      SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.functor.map f :=
  normalized_zero_map_form he _ _ (model.normalizedMap X Y f).factorization

private theorem homology_short_exact_of_boundary_zero
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hz : ZeroOnModTwoHomology model.coefficients T.mor₃) :
    HomologyShortExact model.coefficients T := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift model.coefficients.object
  letI := closedBackground.tensorExact model.coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight model.coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  letI := Functor.isTriangulated_of_iso e
  let F := tensorLeft model.coefficients.object
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang Spectrum := F.map_distinguished T hT
  have hu (n : ℤ) (a : HomotopyGroup n U.obj₃) : a≫U.mor₃=0 := by
    change a≫F.map T.mor₃≫_=0
    change a≫(model.coefficients.object ◁ T.mor₃)≫_=0
    have hh : a≫(model.coefficients.object ◁ T.mor₃)=0 := hz n a
    rw [←Category.assoc,hh,zero_comp]
  intro n
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    have hab' : (a-b)≫U.mor₁=0 := by
      change a≫U.mor₁=b≫U.mor₁ at hab
      rw [Preadditive.sub_comp,hab,sub_self]
    let S := shiftFunctor Spectrum (1:ℤ)
    have hh : S.map (a-b)≫S.map U.mor₁=0 := by
      rw [←Functor.map_comp,hab',Functor.map_zero]
    obtain ⟨d,hd⟩ := U.coyoneda_exact₁ hU (S.map (a-b)) hh
    let eS : Sphere (C:=Spectrum) (n+1) ≅ S.obj (Sphere n) :=
      ((shiftFunctorAdd' Spectrum n 1 (n+1) rfl).app SphereSpectrum)
    have hz' : (eS.hom≫d)≫U.mor₃=0 := hu (n+1) _
    have hd0 : d≫U.mor₃=0 := (cancel_epi eS.hom).mp
      (by simpa only [Category.assoc,comp_zero] using hz')
    have hs0 : S.map (a-b)=0 := hd.trans hd0
    have hab0 : a-b=0 := S.map_injective
      (by simpa only [Functor.map_zero] using hs0)
    exact sub_eq_zero.mp hab0
  · intro a
    constructor
    · intro ha
      obtain ⟨b,hb⟩ := U.coyoneda_exact₂ hU a ha
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,rfl⟩
      change (b≫U.mor₁)≫U.mor₂=0
      rw [Category.assoc,comp_distTriang_mor_zero₁₂ U hU,comp_zero]
  · intro a
    obtain ⟨b,hb⟩ := U.coyoneda_exact₃ hU a (hu n a)
    exact ⟨b,hb.symm⟩

private theorem rotated_nu_boundary_homology_zero :
    ZeroOnModTwoHomology model.coefficients rotatedNuRouteTriangle.h := by
  have hfil : MapFiltrationAtLeast model.classicalTower rotatedNuRouteTriangle.h 1 := by
    by_contra hn
    have he := rotated_nu_h_exponent
    unfold normalizedExponent at he
    simp only [hn,ite_false] at he
    contradiction
  have hfac := ((factorization_filtration_iff rotatedNuRouteTriangle.h 1).mpr hfil)
    1 (by omega) (by omega)
  have hpos {A B : Spectrum} {n : ℕ} {f : A ⟶ B}
      (hh : AdamsMapFactorization model.coefficients n f) : 0<n := by
    cases hh <;> omega
  have hone {A B : Spectrum} {n : ℕ} {f : A ⟶ B}
      (hh : AdamsMapFactorization model.coefficients n f) (hn : n=1) :
      ZeroOnModTwoHomology model.coefficients f := by
    cases hh with
    | single f hf => exact hf
    | prepend f g hf hg => have hp := hpos hg; omega
  exact hone hfac rfl

private theorem rotated_nu_homology_short_exact :
    HomologyShortExact model.coefficients
      (Triangle.mk rotatedNuRouteTriangle.f rotatedNuRouteTriangle.g rotatedNuRouteTriangle.h) :=
  homology_short_exact_of_boundary_zero _ rotatedNuRouteTriangle.distinguished
    rotated_nu_boundary_homology_zero

private def negative_lift_at_one {A B : SyntheticSpectrum} (k : ℕ) (hk : k=1)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    A ⟶ (SyntheticCategory.biShift (0,-1)).obj B := by
  cases hk
  exact negativeLift 1 f

private theorem negative_lift_at_one_factorization {A B : SyntheticSpectrum}
    (k : ℕ) (hk : k=1)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    negative_lift_at_one k hk f ≫ lambdaPow 1 B =
      lambdaToPositivePow k A ≫ f := by
  subst k
  exact negative_lift_factorization 1 f

private def rotated_nu_selected_full_lift : SyntheticFullLift model rotatedNuRouteTriangle.h 1 where
  map := negative_lift_at_one _ rotated_nu_h_exponent
    (model.normalizedMap rotatedNuRouteTriangle.Z (.shift 1 rotatedNuRouteTriangle.X)
      rotatedNuRouteTriangle.h).map
  factorization := (negative_lift_at_one_factorization _ rotated_nu_h_exponent _).trans
    (model.normalizedMap rotatedNuRouteTriangle.Z (.shift 1 rotatedNuRouteTriangle.X)
      rotatedNuRouteTriangle.h).factorization

private def rotated_nu_triangle_lift :
    SyntheticTriangleLift model
      (Triangle.mk rotatedNuRouteTriangle.f rotatedNuRouteTriangle.g rotatedNuRouteTriangle.h) := by
  apply Classical.choose
  apply KIP126.Literature.Standard.triangle_lift _ rotatedNuRouteTriangle.distinguished
  · change MapFiltrationAtLeast model.classicalTower rotatedNuRouteTriangle.h 1
    by_contra hn
    have he := rotated_nu_h_exponent
    unfold normalizedExponent at he
    simp only [hn,ite_false] at he
    contradiction
  · exact rotated_nu_homology_short_exact

private def rotated_nu_source_sphere :
    model.nu.functor.obj (rotatedNuRouteTriangle.Z.obj model.auxiliary) ≅
      Smn (Syn:=SyntheticSpectrum) 4 4 :=
  model.nu.suspensionIso (Sphere (C:=Spectrum) 3) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nuSphereThree model) ≪≫
      (biShiftAddIso (3,3) (1,1) (4,4) (by ext <;> norm_num)).app S_0_0

private theorem rotated_nu_selected_connecting_eq :
    rotated_nu_selected_full_lift.map = rotated_nu_triangle_lift.connecting := by
  let e := rotated_nu_source_sphere
  let a : model.nu.functor.obj (rotatedNuRouteTriangle.Z.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 .sphere).obj model.auxiliary)) :=
    rotated_nu_selected_full_lift.map
  let b : model.nu.functor.obj (rotatedNuRouteTriangle.Z.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 .sphere).obj model.auxiliary)) :=
    rotated_nu_triangle_lift.connecting
  change a=b
  have hk : (e.inv≫(a-b)) ≫
      SyntheticCategory.lam.app _=0 := by
    rw [Category.assoc,Preadditive.sub_comp]
    have hF : a≫SyntheticCategory.lam.app _=model.nu.functor.map rotatedNuRouteTriangle.h := by
      have h := rotated_nu_selected_full_lift.factorization
      rw [lambdaPow_one model.quotients.coherence] at h
      exact h
    have hL : b≫SyntheticCategory.lam.app _=model.nu.functor.map rotatedNuRouteTriangle.h :=
      rotated_nu_triangle_lift.factorization
    rw [hF,hL,sub_self,comp_zero]

  have hz := lambda_one_injective_at_diagonal (.shift 1 .sphere) 4 4 (by omega)
    (e.inv≫(a-b)) hk
  have heq : a-b=0 :=
    (cancel_epi e.inv).mp (by simpa only [comp_zero] using hz)
  exact sub_eq_zero.mp heq

private def zero_positive_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
    (SyntheticCategory.biShift (0,(k:ℤ))).obj A ≅ A :=
  eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≪≫
    SyntheticCategory.biShift_zero.app A

private def zero_negative_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
    (SyntheticCategory.biShift (0,-(k:ℤ))).obj A ≅ A :=
  eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,-(j:ℤ))).obj A) hk) ≪≫
    SyntheticCategory.biShift_zero.app A

private theorem negative_lift_zero_map_form {A B : SyntheticSpectrum} (k : ℕ)
    (hk : k=0) (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hfg : lambdaToPositivePow k A≫f=g) :
    negativeLift k f≫(zero_negative_iso B k hk).hom=g := by
  subst k
  have h := (negative_lift_factorization 0 f).trans hfg
  simpa only [zero_negative_iso,lambdaPow,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,Category.id_comp,Iso.app_hom] using h

private def raw_normalized_connecting {A C D : SyntheticSpectrum} (ef eg eh : ℕ)
    (he : (ef:ℤ)+eg+eh=1)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A) :
    (SyntheticCategory.biShift (0,-(eg:ℤ))).obj C ⟶
      ((SyntheticCategory.biShift (0,(ef:ℤ))).obj A)⟦(1:ℤ)⟧ :=
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map (negativeLift eh h) ≫
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map
      ((SyntheticCategory.biShift (0,-(eh:ℤ))).map σ.hom) ≫
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-(eh:ℤ))).hom.app A) ≫
  (SyntheticCategory.biShift_comp ((1,1)+(0,-(eh:ℤ))) (0,-(eg:ℤ))).hom.app A ≫
  eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj A)
    (show ((1,1)+(0,-(eh:ℤ)))+(0,-(eg:ℤ))=(0,(ef:ℤ))+(1,0) from by
      ext
      · rfl
      · dsimp; omega)) ≫
  (SyntheticCategory.biShift_comp (0,(ef:ℤ)) (1,0)).inv.app A ≫
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _

private theorem raw_connecting_zero_zero_one {A C D : SyntheticSpectrum}
    (ef eg eh : ℕ) (he : (ef:ℤ)+eg+eh=1)
    (hf : ef=0) (hg : eg=0) (hh : eh=1)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A) :
    raw_normalized_connecting ef eg eh he h σ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (zero_positive_iso A ef hf).hom =
      (zero_negative_iso C eg hg).hom ≫ negative_lift_at_one eh hh h ≫
        (SyntheticCategory.biShift (0,-1)).map σ.hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A := by
  subst ef; subst eg; subst eh
  dsimp only [raw_normalized_connecting,zero_positive_iso,zero_negative_iso,
    negative_lift_at_one]
  simp only [eqToHom_refl,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,Category.id_comp]
  have hleft := model.quotients.coherence.left_unit (1,0) A
  have hright := model.quotients.coherence.right_unit (1,0) A
  dsimp only [biShiftAddIso] at hleft hright
  simp only [eqToIso_refl,Iso.trans_refl] at hleft hright
  have hn := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    (SyntheticCategory.biShift_zero.hom.app A)
  dsimp only [Functor.id_obj,Functor.comp_obj,Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [←hn,←hleft,Iso.inv_hom_id_app_assoc,hright]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map,Iso.app_hom]
  rfl

private theorem rotated_normalized_connecting_square :
    normalizedConnecting model rotatedNuRouteTriangle rotated_nu_exponent_sum ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (zero_positive_iso (model.nu.functor.obj (rotatedNuRouteTriangle.X.obj model.auxiliary))
          _ rotated_nu_f_exponent).hom =
    (zero_negative_iso (model.nu.functor.obj (rotatedNuRouteTriangle.Z.obj model.auxiliary))
      _ rotated_nu_g_exponent).hom ≫
        rotated_nu_triangle_lift.connecting ≫
          (model.nu.boundaryLandingIso (rotatedNuRouteTriangle.X.obj model.auxiliary)).hom := by
  erw [←rotated_nu_selected_connecting_eq]
  have h := raw_connecting_zero_zero_one _ _ _ rotated_nu_exponent_sum
    rotated_nu_f_exponent rotated_nu_g_exponent rotated_nu_h_exponent
    (model.normalizedMap rotatedNuRouteTriangle.Z (.shift 1 rotatedNuRouteTriangle.X)
      rotatedNuRouteTriangle.h).map
    (model.nu.suspensionIso (rotatedNuRouteTriangle.X.obj model.auxiliary))
  simpa only [normalizedConnecting,raw_normalized_connecting,rotated_nu_selected_full_lift,
    NuFunctorData.boundaryLandingIso,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,
    Category.assoc] using h

private theorem rotated_nu_normalized_distinguished :
    normalizedTriangle model rotatedNuRouteTriangle rotated_nu_exponent_sum ∈
      distTriang SyntheticSpectrum := by
  let U := Triangle.mk
    (model.nu.functor.map rotatedNuRouteTriangle.f)
    (model.nu.functor.map rotatedNuRouteTriangle.g)
    (rotated_nu_triangle_lift.connecting ≫
      (model.nu.boundaryLandingIso (rotatedNuRouteTriangle.X.obj model.auxiliary)).hom)
  have hU : U ∈ distTriang SyntheticSpectrum := rotated_nu_triangle_lift.distinguished
  let eA := zero_positive_iso
    (model.nu.functor.obj (rotatedNuRouteTriangle.X.obj model.auxiliary)) _ rotated_nu_f_exponent
  let eC := zero_negative_iso
    (model.nu.functor.obj (rotatedNuRouteTriangle.Z.obj model.auxiliary)) _ rotated_nu_g_exponent
  apply isomorphic_distinguished U hU _
  refine Triangle.isoMk (normalizedTriangle model rotatedNuRouteTriangle rotated_nu_exponent_sum)
    U eA (Iso.refl _) eC ?_ ?_ ?_
  · dsimp only [normalizedTriangle,U,Triangle.mk_mor₁]
    simp only [Iso.refl_hom,Category.comp_id]
    simpa only [eA,zero_positive_iso,Iso.trans_hom,eqToIso.hom,Iso.app_hom,Category.assoc] using
      normalized_zero_map _ _ _ rotated_nu_f_exponent
  · dsimp only [normalizedTriangle,U,Triangle.mk_mor₂]
    simp only [Iso.refl_hom,Category.id_comp]
    exact negative_lift_zero_map_form _ rotated_nu_g_exponent _ _
      (model.normalizedMap rotatedNuRouteTriangle.Y rotatedNuRouteTriangle.Z
        rotatedNuRouteTriangle.g).factorization
  · dsimp only [normalizedTriangle,U,Triangle.mk_mor₃]
    exact rotated_normalized_connecting_square

end
end KIP126.ProofTools.Internal.Mahowald
