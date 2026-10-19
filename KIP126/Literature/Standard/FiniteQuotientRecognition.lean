module

import all KIP126.Literature.Standard.FiniteQuotientPositive

/-! Realization detects maps from the actual finite nu source. The
registered realization-kernel comparison and the proved finite lambda
windows are used on the same sphere or nu Cnu source. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

private theorem recognition_lambda_power_precomp_sphere_zero
    (Y : ClassicalObject) (m w : ℤ) (hw : w≤m) (q : ℕ)
    (a : BiHom m w (model.nu.functor.obj (Y.obj model.auxiliary)))
    (ha : lambdaPow q (Smn m w)≫a=0) : a=0 := by
  by_cases hq : q=0
  · subst q
    exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn m w))).mp
      (by simpa only [lambdaPow,comp_zero] using ha)
  · let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
    letI : F.Additive := model.exactness.shiftAdditive (0,-(q:ℤ))
    have hpost : F.map a≫lambdaPow q (model.nu.functor.obj (Y.obj model.auxiliary))=0 := by
      rw [lambdaPow_naturality,ha]
    let eD : F.obj (Smn (Syn:=SyntheticSpectrum) m w) ≅ Smn m (w-(q:ℤ)) :=
      (biShiftAddIso (m,w) (0,-(q:ℤ)) (m,w-(q:ℤ)) (by ext <;> simp [sub_eq_add_neg])).app S_0_0
    let eSD : (F.obj (Smn (Syn:=SyntheticSpectrum) m w))⟦(1:ℤ)⟧ ≅
        Smn (m+1) (w-(q:ℤ)) :=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eD ≪≫
        positive_sphere_suspension_iso m (w-(q:ℤ))
    have hmap : F.map a=0 := positive_lambda_power_injective_of_quotient_vanishing _ _ q
      (fun b => negative_hom_finite_sphere_iso Y q (by omega) (m+1) (w-q)
        (by omega) eSD b) _ hpost
    exact (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-(q:ℤ))).map_injective
      (by simpa only [Functor.map_zero] using hmap)

private theorem recognition_realization_sphere_zero
    (Y : ClassicalObject) (m w : ℤ) (hw : w≤m)
    (a : BiHom m w (model.nu.functor.obj (Y.obj model.auxiliary)))
    (ha : model.recovery.realization.map a=0) : a=0 := by
  obtain ⟨q,hq⟩ := (selected_realization_kernel (.nu Y) m w a).mp ha
  apply recognition_lambda_power_precomp_sphere_zero Y m w hw q a
  simpa only [lambdaMultiply,comp_eq_zero_iff_of_epi] using hq

private theorem recognition_realization_sphere_injective
    (Y : ClassicalObject) (m w : ℤ) (hw : w≤m) :
    Function.Injective (fun a : BiHom m w (model.nu.functor.obj (Y.obj model.auxiliary)) =>
      model.recovery.realization.map a) := by
  letI := realization_additive
  intro a b hab
  dsimp only at hab
  apply sub_eq_zero.mp
  apply recognition_realization_sphere_zero Y m w hw (a-b)
  rw [Functor.map_sub,hab,sub_self]

private theorem recognition_realization_nu_full (X Y : Spectrum) :
    Function.Surjective (fun a : model.nu.functor.obj X ⟶ model.nu.functor.obj Y =>
      model.recovery.realization.map a) := by
  intro g
  let f := model.recovery.nuRealizationIso.inv.app X ≫ g ≫
    model.recovery.nuRealizationIso.hom.app Y
  refine ⟨model.nu.functor.map f, ?_⟩
  apply (cancel_mono (model.recovery.nuRealizationIso.hom.app Y)).mp
  have h := model.recovery.nuRealizationIso.hom.naturality f
  dsimp only [Functor.comp_map,Functor.id_map,Functor.id_obj] at h
  simpa only [f,←Category.assoc,Iso.hom_inv_id_app,Category.id_comp] using h

private theorem recognition_realization_nu_source_iso_full
    {A : SyntheticSpectrum} (X Y : Spectrum)
    (e : A ≅ model.nu.functor.obj X) :
    Function.Surjective (fun a : A ⟶ model.nu.functor.obj Y =>
      model.recovery.realization.map a) := by
  intro g
  obtain ⟨b,hb⟩ := recognition_realization_nu_full X Y
    (model.recovery.realization.map e.inv ≫ g)
  refine ⟨e.hom ≫ b, ?_⟩
  change model.recovery.realization.map b = _ at hb
  change model.recovery.realization.map (e.hom ≫ b) = g
  rw [Functor.map_comp,hb,←Category.assoc,←Functor.map_comp,e.hom_inv_id]
  simp only [CategoryTheory.Functor.map_id,Category.id_comp]

private theorem recognition_realization_full_lower_weight
    (m w : ℤ) (k : ℕ) (Y : SyntheticSpectrum)
    (hfull : Function.Surjective (fun a : BiHom m w Y =>
      model.recovery.realization.map a)) :
    Function.Surjective (fun a : BiHom m (w-k) Y =>
      model.recovery.realization.map a) := by
  intro g
  obtain ⟨a,ha⟩ := hfull ((realization_sphere m w).inv ≫
    (realization_sphere m (w-k)).hom ≫ g)
  refine ⟨lambdaMultiply k a, ?_⟩
  change model.recovery.realization.map a = _ at ha
  change model.recovery.realization.map (lambdaMultiply k a) = g
  have hf : lambdaMultiply k a =
      lambdaMultiply k (𝟙 (Smn (Syn:=SyntheticSpectrum) m w)) ≫ a := by
    dsimp only [lambdaMultiply]
    simp only [Category.assoc,Category.comp_id]
  apply (cancel_epi (realization_sphere m (w-k)).hom).mp
  rw [hf,Functor.map_comp,←Category.assoc,realization_lambda,ha]
  simp only [←Category.assoc,Iso.hom_inv_id,Category.id_comp]

private theorem recognition_realization_full_at_zero (Y : ClassicalObject) :
    Function.Surjective (fun a : BiHom 0 0
        (model.nu.functor.obj (Y.obj model.auxiliary)) =>
      model.recovery.realization.map a) := by
  let e : Smn (Syn:=SyntheticSpectrum) 0 0 ≅ model.nu.functor.obj SphereSpectrum :=
    (SyntheticCategory.biShift_zero.app (S_0_0 : SyntheticSpectrum)) ≪≫
      model.nu.unitIso.symm
  exact recognition_realization_nu_source_iso_full SphereSpectrum
    (Y.obj model.auxiliary) e

private theorem recognition_realization_full_at_one_diagonal (Y : ClassicalObject) :
    Function.Surjective (fun a : BiHom 1 1
        (model.nu.functor.obj (Y.obj model.auxiliary)) =>
      model.recovery.realization.map a) := by
  let e : Smn (Syn:=SyntheticSpectrum) 1 1 ≅
      model.nu.functor.obj (Sphere (C:=Spectrum) 1) :=
    (model.nu.suspensionIso SphereSpectrum ≪≫
      (SyntheticCategory.biShift (1,1)).mapIso model.nu.unitIso).symm
  exact recognition_realization_nu_source_iso_full (Sphere (C:=Spectrum) 1)
    (Y.obj model.auxiliary) e

private theorem recognition_realization_full_at_one_zero (Y : ClassicalObject) :
    Function.Surjective (fun a : BiHom 1 0
        (model.nu.functor.obj (Y.obj model.auxiliary)) =>
      model.recovery.realization.map a) := by
  simpa using recognition_realization_full_lower_weight 1 1 1
    (model.nu.functor.obj (Y.obj model.auxiliary))
    (recognition_realization_full_at_one_diagonal Y)


/-- The exact middle-source argument retains the same map and actual
realization; only the indicated endpoint injectivity and suspended-source
fullness are used. -/
private theorem recognition_realization_zero_middle
    (T : Triangle SyntheticSpectrum) (hT : T ∈ distTriang SyntheticSpectrum)
    (Y : SyntheticSpectrum)
    (hA : ∀ a : T.obj₁ ⟶ Y, model.recovery.realization.map a=0 → a=0)
    (hC : ∀ c : T.obj₃ ⟶ Y, model.recovery.realization.map c=0 → c=0)
    (hSA : Function.Surjective (fun d : T.obj₁⟦(1:ℤ)⟧ ⟶ Y =>
      model.recovery.realization.map d))
    (b : T.obj₂ ⟶ Y) (hb : model.recovery.realization.map b=0) : b=0 := by
  let R := model.recovery.realization
  letI := realization_additive
  letI : R.CommShift ℤ := model.exactness.realizationShift
  letI : R.IsTriangulated := model.exactness.realizationExact
  have hf : T.mor₁≫b=0 := hA _ (by rw [Functor.map_comp,hb,comp_zero])
  obtain ⟨c,hc⟩ := T.yoneda_exact₂ hT b hf
  have hg : R.map T.mor₂≫R.map c=0 := by rw [←Functor.map_comp,←hc]; exact hb
  obtain ⟨d,hd⟩ := (R.mapTriangle.obj T).yoneda_exact₃ (R.map_distinguished T hT)
    (R.map c) hg
  obtain ⟨d',hd'⟩ := hSA ((R.commShiftIso (1:ℤ)).hom.app T.obj₁≫d)
  change R.map d'=(R.commShiftIso (1:ℤ)).hom.app T.obj₁≫d at hd'
  have hcz : R.map (c-T.mor₃≫d')=0 := by
    rw [Functor.map_sub,Functor.map_comp,hd']
    apply sub_eq_zero.mpr
    change R.map c=(R.map T.mor₃≫(R.commShiftIso (1:ℤ)).hom.app T.obj₁)≫d at hd
    simpa only [Category.assoc] using hd
  have hc' : c=T.mor₃≫d' := sub_eq_zero.mp (hC _ hcz)
  rw [hc,hc',←Category.assoc,comp_distTriang_mor_zero₂₃ T hT,zero_comp]

private theorem recognition_realization_zero_of_sphere_iso
    (Y : ClassicalObject) {D : SyntheticSpectrum} (m w : ℤ) (hw : w≤m)
    (e : D ≅ Smn m w)
    (a : D ⟶ model.nu.functor.obj (Y.obj model.auxiliary))
    (ha : model.recovery.realization.map a=0) : a=0 := by
  have hz : e.inv≫a=0 := recognition_realization_sphere_zero Y m w hw _
    (by rw [Functor.map_comp,ha,comp_zero])
  exact (cancel_epi e.inv).mp (by simpa using hz)

private theorem recognition_realization_full_of_source_iso
    {D E Y : SyntheticSpectrum} (e : D ≅ E)
    (hfull : Function.Surjective (fun a : E ⟶ Y => model.recovery.realization.map a)) :
    Function.Surjective (fun a : D ⟶ Y => model.recovery.realization.map a) := by
  intro f
  obtain ⟨a,ha⟩ := hfull (model.recovery.realization.map e.inv≫f)
  change model.recovery.realization.map a=model.recovery.realization.map e.inv≫f at ha
  refine ⟨e.hom≫a,?_⟩
  change model.recovery.realization.map (e.hom≫a)=f
  rw [Functor.map_comp,ha,←Category.assoc,←Functor.map_comp,e.hom_inv_id,
    CategoryTheory.Functor.map_id,Category.id_comp]

/-- Realization has zero kernel on maps from this actual two-cell nu
cofiber into every selected nu target. The distinguished source triangle
is the existing normalized nu-cofiber triangle, with its source casts. -/
private theorem recognition_realization_nu_cofiber_zero
    (Y : ClassicalObject)
    (a : model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary))
    (ha : model.recovery.realization.map a=0) : a=0 := by
  let T := (KIP126.Literature.normalizedTriangle model model.auxiliary.nuRouteTriangle
    nuCofiber_exponent_sum).rotate
  have hT : T ∈ distTriang SyntheticSpectrum := rot_of_distTriang _ nuCofiber_distinguished
  let eA : T.obj₁ ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
    model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  let eC : T.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
        ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (KIP126.Literature.nuSphereThree model) ≪≫
          (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      positive_sphere_suspension_iso 3 4
  let eSA : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eA ≪≫ positive_sphere_suspension_iso 0 0
  let eB : T.obj₂ ≅ model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact SyntheticCategory.biShift_zero.app _
  have hz : eB.hom≫a=0 := recognition_realization_zero_middle T hT _
    (fun b hb => recognition_realization_zero_of_sphere_iso Y 0 0 (by omega) eA b hb)
    (fun c hc => recognition_realization_zero_of_sphere_iso Y 4 4 (by omega) eC c hc)
    (recognition_realization_full_of_source_iso eSA (recognition_realization_full_at_one_zero Y)) _
    (by rw [Functor.map_comp,ha,comp_zero])
  exact (cancel_epi eB.hom).mp (by simpa using hz)

private theorem recognition_realization_nu_cofiber_injective
    (Y : ClassicalObject) :
    Function.Injective (fun a : model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary) => model.recovery.realization.map a) := by
  letI := realization_additive
  intro a b hab
  dsimp only at hab
  apply sub_eq_zero.mp
  apply recognition_realization_nu_cofiber_zero Y (a-b)
  rw [Functor.map_sub,hab,sub_self]

private theorem recognition_realization_reflects_iso_of_end_hom
    (D : SyntheticSpectrum)
    (hinj : Function.Injective (fun a : D ⟶ D => model.recovery.realization.map a))
    (hfull : Function.Surjective (fun a : D ⟶ D => model.recovery.realization.map a))
    (u : D ⟶ D) (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  letI := hRu
  obtain ⟨v,hv⟩ := hfull (inv (model.recovery.realization.map u))
  change model.recovery.realization.map v=inv (model.recovery.realization.map u) at hv
  have huv : u≫v=𝟙 D := hinj (by
    change model.recovery.realization.map (u≫v)=model.recovery.realization.map (𝟙 D)
    rw [Functor.map_comp,hv,CategoryTheory.Functor.map_id,IsIso.hom_inv_id])
  have hvu : v≫u=𝟙 D := hinj (by
    change model.recovery.realization.map (v≫u)=model.recovery.realization.map (𝟙 D)
    rw [Functor.map_comp,hv,CategoryTheory.Functor.map_id,IsIso.inv_hom_id])
  exact ⟨⟨v,huv,hvu⟩⟩

/-- On the actual nu Cnu endomorphisms, invertibility can be detected by
the same realization, without a global conservativity premise. -/
private theorem recognition_realization_nu_cofiber_reflects_iso
    (u : model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) ⟶
      model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  exact recognition_realization_reflects_iso_of_end_hom _
    (recognition_realization_nu_cofiber_injective .nuCofiber)
    (recognition_realization_nu_full _ _) u hRu

private theorem recognition_realization_nu_sphere_injective
    (Y : ClassicalObject) :
    Function.Injective (fun a : model.nu.functor.obj SphereSpectrum ⟶
        model.nu.functor.obj (Y.obj model.auxiliary) => model.recovery.realization.map a) := by
  letI := realization_additive
  intro a b hab
  dsimp only at hab
  let e : model.nu.functor.obj SphereSpectrum ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
    model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  apply sub_eq_zero.mp
  apply recognition_realization_zero_of_sphere_iso Y 0 0 (by omega) e (a-b)
  rw [Functor.map_sub,hab,sub_self]

private theorem recognition_realization_nu_sphere_reflects_iso
    (u : model.nu.functor.obj SphereSpectrum ⟶ model.nu.functor.obj SphereSpectrum)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  exact recognition_realization_reflects_iso_of_end_hom _
    (recognition_realization_nu_sphere_injective .sphere)
    (recognition_realization_nu_full _ _) u hRu

section Generic
universe u v u' v'
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem recognition_local_lambda_pow_isIso (q : ℕ) (M : Syn)
    [IsIso (SyntheticCategory.lam.app M)] : IsIso (lambdaPow q M) := by
  induction q with
  | zero =>
    change IsIso (SyntheticCategory.biShift_zero.hom.app M)
    infer_instance
  | succ n ih =>
    letI := ih
    haveI : IsIso ((lambdaShiftAddIso 1 n (n+1) (Nat.add_comm 1 n)).hom.app M ≫
        lambdaPow (n+1) M) := by
      rw [lambdaPow_succ_comparison]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((lambdaShiftAddIso 1 n (n+1) (Nat.add_comm 1 n)).hom.app M) (lambdaPow (n+1) M)

private theorem recognition_local_lambda_pow_precomp_bijective
    (q : ℕ) (X M : Syn) [IsIso (SyntheticCategory.lam.app M)] :
    Function.Bijective (fun a : X ⟶ M => lambdaPow q X ≫ a) := by
  letI := recognition_local_lambda_pow_isIso q M
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(q:ℤ))
  constructor
  · intro a b hab
    change lambdaPow q X ≫ a = lambdaPow q X ≫ b at hab
    apply ff.map_injective
    apply (cancel_mono (lambdaPow q M)).mp
    rw [lambdaPow_naturality,lambdaPow_naturality,hab]
  · intro b
    let a := ff.preimage (b ≫ inv (lambdaPow q M))
    refine ⟨a,?_⟩
    change lambdaPow q X ≫ a = b
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift (0,-(q:ℤ))).map
        (ff.preimage (b ≫ inv (lambdaPow q M))) ≫ lambdaPow q M = b
    rw [ff.map_preimage]
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

private theorem recognition_localization_lambda_pow_isIso
    (L : LambdaLocalization Syn) (q : ℕ) (X : Syn) :
    IsIso (L.reflector.map (lambdaPow q X)) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  letI : IsIso (SyntheticCategory.lam.app M.obj) := M.property
  have hb := recognition_local_lambda_pow_precomp_bijective q X M.obj
  constructor
  · intro a b hab
    apply (L.adjunction.homEquiv X M).injective
    apply hb.1
    have h := congrArg
      (L.adjunction.homEquiv ((SyntheticCategory.biShift (0,-(q:ℤ))).obj X) M) hab
    simpa only [L.adjunction.homEquiv_naturality_left] using h
  · intro b
    obtain ⟨a,ha⟩ := hb.2
      ((L.adjunction.homEquiv ((SyntheticCategory.biShift (0,-(q:ℤ))).obj X) M) b)
    refine ⟨(L.adjunction.homEquiv X M).symm a,?_⟩
    apply (L.adjunction.homEquiv
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj X) M).injective
    rw [L.adjunction.homEquiv_naturality_left,Equiv.apply_symm_apply]
    exact ha

private theorem recognition_recovery_lambda_pow_isIso
    {C : Type u'} [StableHomotopyCategory.{u',v'} C]
    {N : NuFunctorData C Syn} (R : LambdaRecovery N) (q : ℕ) (X : Syn) :
    IsIso (R.realization.map (lambdaPow q X)) := by
  letI := recognition_localization_lambda_pow_isIso R.localization q X
  change IsIso (R.equivalence.functor.map
    (R.localization.reflector.map (lambdaPow q X)))
  infer_instance

end Generic

private theorem recognition_realization_lambda_pow_isIso
    (q : ℕ) (X : SyntheticSpectrum) :
    IsIso (model.recovery.realization.map (lambdaPow q X)) :=
  recognition_recovery_lambda_pow_isIso model.recovery q X


private theorem recognition_realization_reflects_iso_functor_obj
    (F : SyntheticSpectrum ⥤ SyntheticSpectrum) (G : Spectrum ⥤ Spectrum)
    (hF : F.FullyFaithful) (hG : G.FullyFaithful)
    (e : F⋙model.recovery.realization ≅ model.recovery.realization⋙G)
    (D : SyntheticSpectrum)
    (hD : ∀ u : D ⟶ D, IsIso (model.recovery.realization.map u) → IsIso u)
    (u : F.obj D ⟶ F.obj D)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  let v := hF.preimage u
  have hv : F.map v=u := hF.map_preimage u
  letI := hRu
  have hn := e.hom.naturality v
  change model.recovery.realization.map (F.map v)≫e.hom.app D=
    e.hom.app D≫G.map (model.recovery.realization.map v) at hn
  have heq : G.map (model.recovery.realization.map v)=
      e.inv.app D≫model.recovery.realization.map u≫e.hom.app D := by
    apply (cancel_epi (e.hom.app D)).mp
    simpa only [←Category.assoc,Iso.hom_inv_id_app,Category.id_comp] using hn.symm.trans
      (by rw [hv])
  haveI : IsIso (G.map (model.recovery.realization.map v)) := by rw [heq]; infer_instance
  haveI : IsIso (model.recovery.realization.map v) := hG.isIso_of_isIso_map _
  haveI : IsIso v := hD v inferInstance
  rw [←hv]
  infer_instance

private def recognition_realization_negative_weight_iso (q : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))⋙model.recovery.realization ≅
      model.recovery.realization :=
  NatIso.ofComponents (fun X => by
    letI := recognition_realization_lambda_pow_isIso q X
    exact asIso (model.recovery.realization.map (lambdaPow q X))) (fun f => by
      simp only [Functor.comp_map,asIso_hom,←Functor.map_comp,lambdaPow_naturality])

private def recognition_realization_positive_weight_iso (q : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(q:ℤ))⋙model.recovery.realization ≅
      model.recovery.realization := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(q:ℤ))
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let e : F⋙G ≅ 𝟭 SyntheticSpectrum :=
    biShiftAddIso (0,(q:ℤ)) (0,-(q:ℤ)) (0,0) (by ext <;> simp) ≪≫
      SyntheticCategory.biShift_zero
  exact (Functor.isoWhiskerLeft F (recognition_realization_negative_weight_iso q)).symm ≪≫
    (Functor.associator F G model.recovery.realization).symm ≪≫
    Functor.isoWhiskerRight e model.recovery.realization ≪≫
    Functor.leftUnitor model.recovery.realization

private def recognition_realization_weight_iso (w : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,w)⋙model.recovery.realization ≅
      model.recovery.realization := by
  by_cases hw : 0≤w
  · have he : w=(w.toNat:ℤ) := (Int.toNat_of_nonneg hw).symm
    exact eqToIso (congrArg (fun n : ℤ =>
      SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,n)⋙model.recovery.realization) he) ≪≫
      recognition_realization_positive_weight_iso w.toNat
  · have he : w=-((-w).toNat:ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; omega
    exact eqToIso (congrArg (fun n : ℤ =>
      SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,n)⋙model.recovery.realization) he) ≪≫
      recognition_realization_negative_weight_iso (-w).toNat

private def recognition_realization_bishift_iso (p : ℤ×ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p⋙model.recovery.realization ≅
      model.recovery.realization⋙shiftFunctor Spectrum p.1 := by
  letI : model.recovery.realization.CommShift ℤ := model.exactness.realizationShift
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (p.1,0)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,p.2)
  exact Functor.isoWhiskerRight
      (biShiftAddIso (p.1,0) (0,p.2) p (by ext <;> simp)).symm model.recovery.realization ≪≫
    Functor.associator F G model.recovery.realization ≪≫
    Functor.isoWhiskerLeft F (recognition_realization_weight_iso p.2) ≪≫
    Functor.isoWhiskerRight (SyntheticCategory.biShift_compat p.1) model.recovery.realization ≪≫
    model.recovery.realization.commShiftIso p.1

private theorem recognition_realization_reflects_iso_bishift
    (p : ℤ×ℤ) (D : SyntheticSpectrum)
    (hD : ∀ u : D ⟶ D, IsIso (model.recovery.realization.map u) → IsIso u)
    (u : (SyntheticCategory.biShift p).obj D ⟶ (SyntheticCategory.biShift p).obj D)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  exact recognition_realization_reflects_iso_functor_obj _ _
    (SyntheticCategory.biShift_fullyFaithful p)
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor Spectrum p.1))
    (recognition_realization_bishift_iso p) D hD u hRu

private theorem recognition_realization_reflects_iso_shift
    (n : ℤ) (D : SyntheticSpectrum)
    (hD : ∀ u : D ⟶ D, IsIso (model.recovery.realization.map u) → IsIso u)
    (u : D⟦n⟧ ⟶ D⟦n⟧)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  letI : model.recovery.realization.CommShift ℤ := model.exactness.realizationShift
  exact recognition_realization_reflects_iso_functor_obj _ _
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor SyntheticSpectrum n))
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor Spectrum n))
    (model.recovery.realization.commShiftIso n) D hD u hRu

private theorem recognition_realization_shifted_nu_cofiber_reflects_iso
    (p : ℤ×ℤ) (n : ℤ)
    (u : ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)))⟦n⟧ ⟶
      ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)))⟦n⟧)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  exact recognition_realization_reflects_iso_shift n _
    (fun v hv => recognition_realization_reflects_iso_bishift p _
      recognition_realization_nu_cofiber_reflects_iso v hv) u hRu

private theorem recognition_realization_shifted_nu_sphere_reflects_iso
    (p : ℤ×ℤ) (n : ℤ)
    (u : ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (SphereSpectrum (C:=Spectrum))))⟦n⟧ ⟶
      ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (SphereSpectrum (C:=Spectrum))))⟦n⟧)
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  exact recognition_realization_reflects_iso_shift n _
    (fun v hv => recognition_realization_reflects_iso_bishift p _
      recognition_realization_nu_sphere_reflects_iso v hv) u hRu

/-- Objectwise suspension comparisons, proved by integer induction from
the existing nu suspension iso; no naturality in arbitrary maps is inferred. -/
private theorem recognition_nu_classical_shift_iso_exists (Y : ClassicalObject) (p : ℤ) :
    Nonempty (model.nu.functor.obj ((ClassicalObject.shift p Y).obj model.auxiliary) ≅
      (SyntheticCategory.biShift (p,p)).obj (model.nu.functor.obj (Y.obj model.auxiliary))) := by
  induction p using Int.induction_on with
  | zero =>
    exact ⟨model.nu.functor.mapIso ((shiftFunctorZero Spectrum ℤ).app (Y.obj model.auxiliary)) ≪≫
      (SyntheticCategory.biShift_zero.app _).symm⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    exact ⟨model.nu.functor.mapIso
        ((shiftFunctorAdd' Spectrum (i:ℤ) 1 ((i:ℤ)+1) rfl).app (Y.obj model.auxiliary)) ≪≫
      model.nu.suspensionIso ((ClassicalObject.shift i Y).obj model.auxiliary) ≪≫
      (SyntheticCategory.biShift (1,1)).mapIso e ≪≫
      (SyntheticCategory.biShift_comp ((i:ℤ),(i:ℤ)) (1,1)).app _⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    let A := model.nu.functor.obj ((ClassicalObject.shift (-((i:ℤ))-1) Y).obj model.auxiliary)
    let eStep : model.nu.functor.obj ((ClassicalObject.shift (-((i:ℤ))) Y).obj model.auxiliary) ≅
        (SyntheticCategory.biShift (1,1)).obj A :=
      model.nu.functor.mapIso
        ((shiftFunctorAdd' Spectrum (-((i:ℤ))-1) 1 (-((i:ℤ))) (by omega)).app
          (Y.obj model.auxiliary)) ≪≫ model.nu.suspensionIso _
    refine ⟨(SyntheticCategory.biShift_zero.app A).symm ≪≫
      eqToIso (congrArg (fun δ => (SyntheticCategory.biShift δ).obj A)
        (show (0,0)=(1,1)+(-1,-1) by ext <;> norm_num)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (-1,-1)).symm.app A ≪≫
      (SyntheticCategory.biShift (-1,-1)).mapIso eStep.symm ≪≫
      (SyntheticCategory.biShift (-1,-1)).mapIso e ≪≫
      (SyntheticCategory.biShift_comp (-((i:ℤ)),-((i:ℤ))) (-1,-1)).app _ ≪≫ ?_⟩
    exact eqToIso (by simp [sub_eq_add_neg])

private theorem recognition_realization_reflects_iso_of_obj_iso
    {D E : SyntheticSpectrum} (e : D ≅ E)
    (hE : ∀ v : E ⟶ E, IsIso (model.recovery.realization.map v) → IsIso v)
    (u : D ⟶ D) (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  let v := e.inv≫u≫e.hom
  letI := hRu
  haveI : IsIso (model.recovery.realization.map v) := by
    dsimp only [v]
    rw [Functor.map_comp,Functor.map_comp]
    infer_instance
  haveI : IsIso v := hE v inferInstance
  have heq : u=e.hom≫v≫e.inv := by simp [v,Category.assoc]
  rw [heq]
  infer_instance

/-- The proved finite-source recognition property is stable under every
classical shift of that same nu object; it does not assert recognition on
the detector without its own base proof. -/
private theorem recognition_realization_nu_classical_shift_reflects_iso
    (Y : ClassicalObject) (p : ℤ)
    (hY : ∀ v : model.nu.functor.obj (Y.obj model.auxiliary) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary),
      IsIso (model.recovery.realization.map v) → IsIso v)
    (u : model.nu.functor.obj ((ClassicalObject.shift p Y).obj model.auxiliary) ⟶
      model.nu.functor.obj ((ClassicalObject.shift p Y).obj model.auxiliary))
    (hRu : IsIso (model.recovery.realization.map u)) : IsIso u := by
  obtain ⟨e⟩ := recognition_nu_classical_shift_iso_exists Y p
  exact recognition_realization_reflects_iso_of_obj_iso e
    (fun v hv => recognition_realization_reflects_iso_bishift (p,p) _ hY v hv) u hRu

end
end KIP126.Literature.Standard
