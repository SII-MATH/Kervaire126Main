module
public import KIP126.Main.Conditions
public import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.AdamsSynthetic.MappingDetection
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.DetectionOperations
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations KIP126.Main.Internal
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem two_torsion_not_odd {X Y : Spectrum} (a : X ⟶ Y)
    (h2 : a+a=0) (hne : a≠0) : ¬IsOddTorsionMap a := by
  rintro ⟨n,hn,_,hz⟩
  obtain ⟨k,hk⟩ := hn
  rw [hk,add_nsmul,mul_comm 2 k,mul_nsmul,two_nsmul,←smul_add,h2,smul_zero,zero_add,one_nsmul] at hz
  exact hne hz

private theorem sphere_map_filtration_iff (m s : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum) :
    MapAdamsFiltration model.classicalTower a s ↔
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m := by
  change (∃ b, b ≫ (model.classicalTower.tower SphereSpectrum).projection s.toNat = a) ↔
    ∃ b, b ≫ (model.classicalTower.tower SphereSpectrum).projection s = a
  simp only [AbstractAdamsTower.projection, Int.toNat_natCast]
  rfl

private theorem homotopy_filtration_regrade (n m s : ℤ) (h : n=m)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum) :
    eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫ a ∈
        (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s n ↔
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m := by
  subst m
  simp only [eqToHom_refl,Category.id_comp]

private theorem sphere_nonodd_detection (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ¬IsOddTorsionMap a) :
    ∃ (s t : ℤ) (hm : t-s=m) (x : model.classical.sphere.Page 2 (s,t)),
      NonzeroSurvival model.classical.sphere (s,t) x ∧
      ClassicalDetects (model.classicalConvergence .sphere) (s,t) x
        (eqToHom (congrArg (Sphere (C := Spectrum)) hm) ≫ a) := by
  obtain ⟨s,hs,hs'⟩ := KIP126.AdamsSynthetic.Standard.finite_filtration_of_not_odd
    (IsFiniteSpectrum.shift m IsFiniteSpectrum.sphere) IsFiniteSpectrum.sphere a ha
  have hmem := (sphere_map_filtration_iff m s a).mp hs
  have hnot : a ∉ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule (s+1) m :=
    fun h => hs' ((sphere_map_filtration_iff m (s+1) a).mpr h)
  have hx := nonzeroClassicalDetection_of_exact (model.classicalConvergence .sphere)
    (s,m+s) (eqToHom (congrArg (Sphere (C := Spectrum)) (add_sub_cancel_right m s)) ≫ a)
    ((homotopy_filtration_regrade _ m s (add_sub_cancel_right m s) a).mpr hmem)
    (fun h => hnot ((homotopy_filtration_regrade _ m (s+1) (add_sub_cancel_right m s) a).mp h))
  obtain ⟨d⟩ := hx
  exact ⟨s,m+s,add_sub_cancel_right m s,d.pageElement,⟨d.representative,rfl,d.nonzero⟩,d.detects⟩

private theorem survives_of_nonzero_survival (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p)
    (hx : NonzeroSurvival model.classical.sphere p x) :
    SurvivesTo model.classical.sphere r p x := by
  obtain ⟨z,hz,hne⟩ := hx
  let D := model.classical.sphere.ssData p
  let n : WithTop ℕ := ↑(r-model.classical.sphere.r₀).toNat
  let zf := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  refine ⟨D.pageπ n zf,⟨hr,zf,?_,rfl⟩,?_⟩
  · change (Subobject.ofLE (D.Z n) (D.Z _) _ ≫ D.pageπ _) zf=x
    dsimp only [zf]
    rw [←CategoryTheory.comp_apply, ←Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  · intro hzero
    apply hne
    exact (D.infinity_projection_eq_of_page_projection_eq n z 0
      (by simpa only [zf,map_zero,ModuleCat.comp_apply] using hzero)).trans (map_zero _)

private theorem nonzero_survival_not_boundary (s t b : ℤ) (hb : 1≤b)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : NonzeroSurvival model.classical.sphere (s,t) x) :
    x ∉ boundaries model .sphere b (s,t) := by
  intro hmem
  obtain ⟨y,hy,hne⟩ := survives_of_nonzero_survival (b+1) (by omega) (s,t) x hx
  have hzero : RepresentsOnPage model.classical.sphere (b+1) (s,t) x 0 :=
    KIP126.ProofTools.representsOnPage_of_congruent model .sphere (by omega)
      (RepresentsOnPage.zero (by omega))
      ⟨by omega, by simpa only [add_sub_cancel_right,sub_zero] using hmem⟩
  exact hne (hy.unique hzero)

private theorem sphere_infinity_nonzero_of_survival (s t : ℤ) (k : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : NonzeroSurvival model.classical.sphere (s,t) x)
    (e : (model.family.sphere.sequence.ssData (s,t,t-k)).eInfty)
    (he : HasInfinityRepresentative model.family.sphere 2 (s,t,t-k)
      (model.comparison.sphereE2 s t k x) e) : e≠0 := by
  have hn := family_infinity_representative_map model.nu.unitIso.inv (s,t,t-k) _ _ he
  have hl := sphere_label_to_nu k s t x
  change familyPageMap model.family model.nu.unitIso.inv 2 (s,t,t-k)
    (model.comparison.sphereE2 s t k x)=_ at hl
  rw [hl] at hn
  obtain ⟨hx',hf⟩ := (nu_target_label_iff s t k x _).mp hn
  intro hz
  rw [hz,map_zero,map_zero] at hf
  have hmem : x ∈ boundaries model .sphere (1+t-(t-k)) (s,t) :=
    (subquotientClass_eq_zero_iff _ _ ⟨x,hx'⟩).mp hf.symm
  exact nonzero_survival_not_boundary s t _ (by omega) x hx hmem

private theorem lambda_preserves_infinite {m w : ℤ}
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a) (k : ℕ) :
    ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s (lambdaMultiply k a) := by
  intro s
  obtain ⟨b,hb⟩ := ha s
  refine ⟨lambdaMultiply k b,?_⟩
  change b ≫ (model.syntheticTower.tower _).projection s=a at hb
  change lambdaMultiply k b ≫ (model.syntheticTower.tower _).projection s=lambdaMultiply k a
  simpa only [lambdaMultiply,Category.assoc] using congrArg (lambdaMultiply k) hb

private theorem sphere_detected_survival_not_infinite (s t : ℤ) (k : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : NonzeroSurvival model.classical.sphere (s,t) x)
    (a : BiHom (t-s) (t-k) (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (s,t,t-k)
      (model.comparison.sphereE2 s t k x) a)
    (hall : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a) : False := by
  have hf : FiltrationAtLeast model.syntheticTower (s+1) a :=
    model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t-k)
      (by omega : s+1 ≤ ((s+1).toNat:ℤ)) (hall (s+1).toNat)
  have hz : Detects (model.convergence .sphere) (s,t,t-k) 0 0 :=
    ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,0,map_zero _,by simp only [map_zero]⟩
  have hza := KIP126.Main.Internal.Choice.detects_of_difference_in_next_filtration
    (model.convergence .sphere) (s,t,t-k) hz (by simpa only [sub_zero] using hf)
  obtain ⟨e,he,he0⟩ := detects_infinity_equal .sphere (s,t,t-k) a _ 0 ha hza
  exact sphere_infinity_nonzero_of_survival s t k x hx e he
    (he0.unique (HasInfinityRepresentative.zero _ 2 (by decide) _))
private theorem realize_lambda {m w : ℤ} (k : ℕ)
    (b : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    Standard.realizeSphere m (w-k) (lambdaMultiply k b)=Standard.realizeSphere m w b := by
  have hb : lambdaMultiply k b=lambdaMultiply k (𝟙 (Smn m w)) ≫ b := by
    simp only [lambdaMultiply,Category.comp_id,Category.assoc]
  rw [hb]
  change (Standard.realization_sphere m (w-k)).hom ≫ model.recovery.realization.map
      (lambdaMultiply k (𝟙 (Smn m w)) ≫ b) ≫ model.recovery.realization.map model.nu.unitIso.inv ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum =
    (Standard.realization_sphere m w).hom ≫ model.recovery.realization.map b ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
  simp only [Functor.map_comp,←Category.assoc]
  rw [Standard.realization_lambda]

private theorem realize_lift {m w : ℤ} (b : BiHom m w (nuZero model .sphere)) :
    Standard.realizeSphere m w
      (b ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom)=
        Standard.realizeNu .sphere b := by
  change (Standard.realization_sphere m w).hom ≫ model.recovery.realization.map
      (b ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum =
    (Standard.realization_sphere m w).hom ≫ model.recovery.realization.map b ≫
      model.recovery.realization.map (SyntheticCategory.biShift_zero.hom.app _) ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum
  simp only [Functor.map_comp,Category.assoc]
  rw [←Category.assoc (model.recovery.realization.map model.nu.unitIso.hom),
    ←Functor.map_comp,Iso.hom_inv_id,CategoryTheory.Functor.map_id,Category.id_comp]


private theorem prescribed_sphere_lift (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (α : HomotopyGroup (C := Spectrum) (t-s) SphereSpectrum)
    (hx : NonzeroSurvival model.classical.sphere (s,t) x)
    (hdet : ClassicalDetects (model.classicalConvergence .sphere) (s,t) x α) :
    ∃ b : BiHom (t-s) t (S_0_0 : SyntheticSpectrum),
      sphereFirstQuotient model s t (quotientClass 1 b)=x ∧
      Standard.realizeSphere (t-s) t b=α := by
  obtain ⟨b0,hb0,hr0⟩ := Standard.selected_realization_prescribed_lift .sphere s t x α hx hdet
  let f := SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  let b : BiHom (t-s) t (S_0_0 : SyntheticSpectrum) := b0 ≫ f
  refine ⟨b,?_,?_⟩
  · have hc : quotientClass 1 b=quotientClass 1 b0 ≫ XModLambdaN.map f 1 := by
      unfold quotientClass
      simp only [b,Category.assoc]
      exact congrArg (fun h => b0 ≫ h) (XModLambdaN.incl_naturality f 1)
    rw [hc,hb0]
    exact KIP126.ProofTools.Operations.sphere_first_quotient_label s t _
  · exact (realize_lift b0).trans hr0
private def lambdaAt (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) : BiHom m v X :=
  (biShiftAddIso (m,w) (0,-(n:ℤ)) (m,v) h).inv.app S_0_0 ≫
    lambdaPow n (Smn m w) ≫ a

private theorem lambdaAt_heq (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaAt m n w v h a) (lambdaMultiply n a) := by
  unfold lambdaAt lambdaMultiply
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    Category.assoc,eqToHom_comp_heq_iff,heq_eqToHom_comp_iff]
  rfl

private theorem multiply_heq {m w w' : ℤ} {X : SyntheticSpectrum} (n : ℕ)
    (h : w=w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    HEq (lambdaMultiply n a) (lambdaMultiply n b) := by
  subst w'
  cases hab
  rfl

private theorem lambda_multiply_compose {m w : ℤ} {X : SyntheticSpectrum}
    (k n : ℕ) (a : BiHom m w X) :
    HEq (lambdaMultiply n (lambdaMultiply k a)) (lambdaMultiply (k+n) a) := by
  let v := w-(k:ℤ)
  let u := v-(n:ℤ)
  let hk : (m,w)+(0,-(k:ℤ))=(m,v) := by ext <;> dsimp [v] <;> omega
  let hn : (m,v)+(0,-(n:ℤ))=(m,u) := by ext <;> dsimp [u] <;> omega
  let hkn : (m,w)+(0,-((k+n:ℕ):ℤ))=(m,u) := by ext <;> dsimp [u,v] <;> omega
  have ha := shift_assoc_inv model.quotients.coherence (m,w) (0,-(k:ℤ)) (0,-(n:ℤ))
    (m,v) (0,-((k+n:ℕ):ℤ)) (m,u)
    hk (by ext <;> dsimp <;> omega) hn hkn (S_0_0 : SyntheticSpectrum)
  have heq : lambdaAt m n v u hn (lambdaAt m k w v hk a) =
      lambdaAt m (k+n) w u hkn a := by
    unfold lambdaAt
    erw [←reassoc_of% (lambdaPow_naturality n
      ((biShiftAddIso (m,w) (0,-(k:ℤ)) (m,v) hk).inv.app (S_0_0 : SyntheticSpectrum)))]
    erw [←reassoc_of% (lambdaPow_naturality n (lambdaPow k (Smn m w)))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add model.quotients.coherence k n (k+n) rfl (Smn m w)]
    simp only [lambdaShiftAddIso, lambdaDegree, Category.assoc]
    rfl
  have houter := lambdaAt_heq m n v u hn (lambdaAt m k w v hk a)
  have hinner := multiply_heq n (by rfl : v=w-(k:ℤ)) (lambdaAt_heq m k w v hk a)
  exact (houter.trans hinner).symm.trans ((heq_of_eq heq).trans (lambdaAt_heq m (k+n) _ _ hkn a))

private theorem infinite_regrade {m w w' : ℤ} (h : w=w')
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a) :
    ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s (homotopyRegrade rfl h a) := by
  subst w'
  exact ha

private theorem infinite_heq {m w w' : ℤ} (h : w=w')
    {a : BiHom m w (S_0_0 : SyntheticSpectrum)}
    {b : BiHom m w' (S_0_0 : SyntheticSpectrum)} (hab : HEq a b)
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a) :
    ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s b := by
  subst w'
  cases hab
  exact ha

private theorem regrade_heq {m w w' : ℤ} (h : w=w')
    (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    HEq (homotopyRegrade rfl h a) a := by
  subst w'
  rfl

private theorem realize_regrade {m w w' : ℤ} (h : w=w')
    (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    Standard.realizeSphere m w' (homotopyRegrade rfl h a) =
      Standard.realizeSphere m w a := by
  subst w'
  rfl

private theorem realize_zero_iff {m w : ℤ}
    (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    Standard.realizeSphere m w a=0 ↔ model.recovery.realization.map a=0 := by
  change (Standard.realization_sphere m w).hom ≫ model.recovery.realization.map a ≫
    model.recovery.realization.map model.nu.unitIso.inv ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum = 0 ↔ _
  simp only [Limits.comp_eq_zero_iff_of_epi]
  constructor
  · intro h
    apply (cancel_mono (model.recovery.realization.map model.nu.unitIso.inv ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum)).mp
    simpa only [Category.assoc,zero_comp] using h
  · intro h
    rw [h,zero_comp]

private theorem infinite_realization_odd {m w : ℤ}
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a) :
    IsOddTorsionMap (Standard.realizeSphere m w a) := by
  by_contra hnot
  let α := Standard.realizeSphere m w a
  obtain ⟨s,t,hm,x,hx,hdet⟩ := sphere_nonodd_detection m α hnot
  subst m
  have hdet' : ClassicalDetects (model.classicalConvergence .sphere) (s,t) x α := by
    simpa only [eqToHom_refl,Category.id_comp] using hdet
  obtain ⟨b,hb,hr⟩ := prescribed_sphere_lift s t x α hx hdet'
  let v := min w t
  let ka := (w-v).toNat
  let kb := (t-v).toNat
  have hka : (ka:ℤ)=w-v := Int.toNat_of_nonneg (by dsimp [v]; omega)
  have hkb : (kb:ℤ)=t-v := Int.toNat_of_nonneg (by dsimp [v]; omega)
  have hwa : w-(ka:ℤ)=v := by omega
  have hwb : t-(kb:ℤ)=v := by omega
  let a0 : BiHom (t-s) v (S_0_0 : SyntheticSpectrum) :=
    homotopyRegrade rfl hwa (lambdaMultiply ka a)
  let b0 : BiHom (t-s) v (S_0_0 : SyntheticSpectrum) :=
    homotopyRegrade rfl hwb (lambdaMultiply kb b)
  have ha0 : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a0 :=
    infinite_regrade hwa _ (lambda_preserves_infinite a ha ka)
  have hra : Standard.realizeSphere (t-s) v a0=α :=
    (realize_regrade hwa _).trans (realize_lambda ka a)
  have hrb : Standard.realizeSphere (t-s) v b0=α :=
    (realize_regrade hwb _).trans ((realize_lambda kb b).trans hr)
  have hdiff : Standard.realizeSphere (t-s) v (a0-b0)=0 := by
    rw [map_sub,hra,hrb,sub_self]
  obtain ⟨N,hN⟩ := (Standard.selected_realization_kernel .sphere (t-s) v (a0-b0)).mp
    ((realize_zero_iff _).mp hdiff)
  have heq : lambdaMultiply N a0=lambdaMultiply N b0 := by
    apply sub_eq_zero.mp
    simpa only [lambdaMultiply,Preadditive.comp_sub] using hN
  have hh := lambda_preserves_infinite a0 ha0 N
  rw [heq] at hh
  have hcomp : HEq (lambdaMultiply N b0) (lambdaMultiply (kb+N) b) :=
    (multiply_heq N hwb.symm (regrade_heq hwb _)).trans (lambda_multiply_compose kb N b)
  have hall : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q (lambdaMultiply (kb+N) b) :=
    infinite_heq (by push_cast; omega : v-(N:ℤ)=t-((kb+N:ℕ):ℤ)) hcomp hh
  have hbdet := model.sphereDetectionCompatible.homotopy_lambda s t (kb+N) b
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient s t (quotientClass 1 b)=_ at hb
  rw [hb] at hbdet
  exact sphere_detected_survival_not_infinite s t (kb+N) x hx _ hbdet hall

end
end KIP126.Main.Internal.High125
