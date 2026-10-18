module
public import KIP126.Main.Conditions
public import KIP126.AdamsSynthetic.Standard.ClassicalSupport
public import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.AdamsSynthetic.MappingDetection
import all KIP126.Main.Internal.Choice.LambdaInjectivity
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.High125.Finite
import all KIP126.Main.Internal.High125.Tail
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Choice.Filtration
/-! Original high125 filtration argument, Main/Solution/Computation/High125
and Route/CofiberAndFiltration, bbac1fc05843 (MIT). Finite calculations are
transported back to the fixed actual sphere. Infinite tails use the sourced
vanishing line and the existing separation/boundedness interfaces. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated KIP126.Core.Algebra KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature KIP126.Main.Internal.Selected KIP126.Main.Internal.Choice
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000

private theorem stem125_page_five_tail (s : ℤ) (hs : 26 ≤ s) :
    Subsingleton (model.classical.sphere.Page 5 (s,125+s)) := by
  by_cases h64 : s ≤ 64
  · have h := stem125_e5_zero_finite s.toNat (by omega) (by omega)
    rw [Normalized.sequence_eq] at h
    simpa only [KIP126.Computation.Table.sequence,KIP126.Computation.Table.object,
      Int.toNat_of_nonneg (by omega : 0≤s),add_comm] using h
  · apply page_subsingleton_of_le model.classical.sphere 2 5 s (125+s) (by decide) (by decide)
    exact Standard.sphereVanishing s (125+s) (by omega) (by omega)

private theorem stem125_page_six_middle (s : ℤ) (hs : 15 ≤ s) (hs' : s < 25) :
    Subsingleton (model.classical.sphere.Page 6 (s,125+s)) := by
  have h : Subsingleton (Normalized.sphere.Page 6 (s.toNat,(s.toNat:ℤ)+125)) := by
    by_cases h20 : s < 20
    · exact stem125_sixth_pages_15_19 s.toNat (by omega) (by omega)
    · exact stem125_sixth_pages_20_24 s.toNat (by omega) (by omega)
  change Subsingleton ((Normalized.sequence .sphere).Page 6 _) at h
  rw [Normalized.sequence_eq] at h
  simpa only [KIP126.Computation.Table.sequence,KIP126.Computation.Table.object,
    Int.toNat_of_nonneg (by omega : 0≤s),add_comm] using h

private theorem synthetic_tail_grade_zero (s : ℤ) (hs : 26 ≤ s) :
    IsZero (model.family.sphere.sequence.ssData (s,125+s,130)).eInfty := by
  apply sphere_infinity_zero_of_permanent_quotient_zero s (125+s) 130 (by omega)
  exact permanent_quotient_zero_of_page_zero .sphere 5 _ (by decide) (by omega)
    (s,125+s) (stem125_page_five_tail s hs)

private theorem synthetic_middle_grade_zero (s : ℤ) (hs : 15 ≤ s) (hs' : s < 25) :
    IsZero (model.family.sphere.sequence.ssData (s,125+s,130)).eInfty := by
  apply sphere_infinity_zero_of_permanent_quotient_zero s (125+s) 130 (by omega)
  exact permanent_quotient_zero_of_page_zero .sphere 6 _ (by decide) (by omega)
    (s,125+s) (stem125_page_six_middle s hs hs')

theorem synthetic_filtration_fifteen_to_twentyfive
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 15 a) :
    FiltrationAtLeast model.syntheticTower 25 a := by
  have step (s : ℕ) (hs : 15≤s) (hs' : s<25)
      (h : FiltrationAtLeast model.syntheticTower s a) :
      FiltrationAtLeast model.syntheticTower (s+1) a :=
    filtration_step_of_infinity_zero (model.convergence .sphere) s 125 130
      (synthetic_middle_grade_zero s (by omega) (by omega)) a h
  have all (s : ℕ) (hs : 15≤s) (hs' : s≤25) : FiltrationAtLeast model.syntheticTower s a := by
    induction s,hs using Nat.le_induction with
    | base => exact ha
    | succ n hn ih => exact_mod_cast step n hn (by omega) (ih (by omega))
  exact all 25 (by decide) (by decide)

theorem synthetic_filtration26_infinite (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 26 a) :
    ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a := by
  intro s
  by_cases hs : s≤26
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (125,130) (by omega) ha
  · have all (s : ℕ) (hs : 26≤s) : FiltrationAtLeast model.syntheticTower s a := by
      induction s,hs using Nat.le_induction with
      | base => exact ha
      | succ n hn ih =>
        have h := filtration_step_of_infinity_zero (model.convergence .sphere) n 125 130
          (synthetic_tail_grade_zero n (by omega)) a ih
        simpa only [Nat.cast_add,Nat.cast_one] using h
    exact all s (by omega)

private theorem classical_tail_grade_zero (s : ℤ) (hs : 26≤s) :
    Subsingleton (model.classical.sphere.ssData (s,125+s)).eInfty := by
  let P := model.classical.sphere.ssData (s,125+s)
  let n : WithTop ℕ := ↑(5-model.classical.sphere.r₀).toNat
  have hp : Subsingleton (P.page n) := stem125_page_five_tail s hs
  have hall (e : P.eInfty) : e=0 := by
    haveI : Epi (P.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (P.pageπ ⊤)).mp inferInstance e
    have h := P.infinity_projection_eq_of_page_projection_eq n z 0 (hp.elim _ _)
    simpa only [map_zero] using h
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem classical_filtration_step (s : ℤ) (hs : 26≤s)
    (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 125) :
    a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule (s+1) 125 := by
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  haveI := classical_tail_grade_zero s hs
  have e : (model.classical.sphere.ssData (s,125+s)).eInfty ≅ F.associatedGraded s 125 := by
    simpa only [add_sub_cancel_right,F,ClassicalObject.obj,ClassicalAdamsFamily.sphere] using (model.classicalConvergence .sphere).identification (s,125+s)
  haveI : Subsingleton (F.associatedGraded s 125) := (ModuleCat.mono_iff_injective e.inv).mp inferInstance |>.subsingleton
  have hm : a ∈ (ModuleCat.subobjectModule _) (F.F s 125) := by
    simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  obtain ⟨b,hb⟩ := hm
  have hz : F.toAssociatedGraded s 125 b=0 := Subsingleton.elim _ _
  have hn := (F.toAssociatedGraded_eq_zero_iff s 125 b).mp hz
  rw [hb] at hn
  simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hn

theorem classical_filtration26_odd_torsion (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 26 125) :
    IsOddTorsionMap a := by
  have all (s : ℕ) (hs : 26≤s) :
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 125 := by
    induction s,hs using Nat.le_induction with
    | base => exact ha
    | succ k hk ih =>
      simpa only [Nat.cast_add,Nat.cast_one] using classical_filtration_step k (by omega) a ih
  apply KIP126.AdamsSynthetic.Standard.classical_sphere_separated 125 a
  intro s
  by_cases hs : s≤26
  · exact (model.classicalTower.tower SphereSpectrum).filtrationSubmodule_antitone 125 (by omega) ha
  · exact all s (by omega)


/-! Actual infinite-filtration kernels, reconstructed from the same finite
λ cofibers, BHS lifts and ordinary finite-map separation. -/
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
private theorem bridge_realize_lambda {m w : ℤ} (k : ℕ)
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

private theorem bridge_realize_lift {m w : ℤ} (b : BiHom m w (nuZero model .sphere)) :
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
    exact KIP126.ProofTools.Internal.Mahowald.sphere_first_quotient_label s t _
  · exact (bridge_realize_lift b0).trans hr0
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
    (realize_regrade hwa _).trans (bridge_realize_lambda ka a)
  have hrb : Standard.realizeSphere (t-s) v b0=α :=
    (realize_regrade hwb _).trans ((bridge_realize_lambda kb b).trans hr)
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

private theorem route_mem_top_cycles (D : SSData (ModuleCat ℤ)) (a : D.V)
    (ha : ∀ n : ℕ, a ∈ ModuleCat.subobjectModule _ (D.Z n)) :
    a ∈ ModuleCat.subobjectModule _ (D.Z ⊤) := by
  have hspan : (ModuleCat.subobjectModule _).symm (Submodule.span ℤ {a}) ≤ D.Z ⊤ := by
    apply D.Z_top_greatest
    intro n
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    simp only [OrderIso.apply_symm_apply, Submodule.span_le, Set.singleton_subset_iff]
    exact ha n
  have h := (ModuleCat.subobjectModule D.V).monotone hspan
  apply h
  rw [OrderIso.apply_symm_apply]
  exact Submodule.subset_span (by simp)

private theorem route_common_cycle_of_finite_cycles
    (D : SSData (ModuleCat ℤ)) (x : D.page 0)
    (hx : ∀ n : ℕ, ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = x) :
    ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = x := by
  obtain ⟨z₀,hz₀⟩ := hx 0
  have hz₀' : D.pageπ 0 z₀ = x := by
    change (Subobject.ofLE (D.Z 0) (D.Z 0) (le_refl _) ≫ D.pageπ 0) z₀ = x at hz₀
    simpa only [Subobject.ofLE_refl, Category.id_comp] using hz₀
  have hall (n : ℕ) : (D.Z 0).arrow z₀ ∈ ModuleCat.subobjectModule _ (D.Z n) := by
    obtain ⟨z,hz⟩ := hx n
    let j := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)
    have hkernel : D.pageπ 0 (z₀-j z)=0 := by
      rw [map_sub, hz₀']
      change x - (j ≫ D.pageπ 0) z = 0
      rw [hz, sub_self]
    have hk := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hkernel
    have hk' : (D.Z 0).arrow (z₀-j z) ∈ ModuleCat.subobjectModule _ (D.Z n) :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))) hk
    have hj : (D.Z 0).arrow (j z) = (D.Z n).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti bot_le)) z
    have he : (D.Z 0).arrow z₀ =
        (D.Z 0).arrow (z₀-j z) + (D.Z n).arrow z := by
      rw [map_sub,hj]
      abel
    rw [he]
    exact Submodule.add_mem _ hk' ⟨z,rfl⟩
  obtain ⟨zInf,hzInf⟩ := route_mem_top_cycles D ((D.Z 0).arrow z₀) hall
  have he : (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le)) zInf = z₀ := by
    apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
    exact (ConcreteCategory.congr_hom
      (Subobject.ofLE_arrow (D.Z_anti (show (0:WithTop ℕ)≤⊤ from le_top))) zInf).trans hzInf
  refine ⟨zInf,?_⟩
  rw [ModuleCat.comp_apply,he,hz₀']

private theorem route_permanent_of_all_reaches
    (X : ClassicalObject) (p : ℤ×ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hx : ∀ n : ℕ, ReachesPage (model.classical.obj (X.obj model.auxiliary))
      ((n:ℤ)+2) p x) : ClassicalPermanentCycle model X p x := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let D := E.ssData p
  let e : D.page 0 ≅ E.Page 2 p := eqToIso (by
    dsimp only [Page, D, E]
    rw [model.classical.firstPage]
    rfl)
  have hall (n : ℕ) : ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = e.inv x := by
    have hc := ((KIP126.ProofTools.isCycle_iff_reaches model X ((n:ℤ)+2)
      (by omega) p x).mpr (hx n)).2
    have hn : (((n:ℤ)+2-1)-1).toNat=n := by omega
    change x ∈ LinearMap.range (cycleLabel model X (↑(((n:ℤ)+2-1)-1).toNat) p).hom at hc
    rw [hn] at hc
    obtain ⟨z,hz⟩ := hc
    refine ⟨z, ?_⟩
    apply e.toLinearEquiv.injective
    change e.hom ((Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z) = e.hom (e.inv x)
    rw [show e.hom (e.inv x)=x from e.toLinearEquiv.apply_symm_apply x]
    exact hz
  obtain ⟨z,hz⟩ := route_common_cycle_of_finite_cycles D (e.inv x) hall
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have normalize (n : WithTop ℕ) (hn : n=0) :
      Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n =
      Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0 ≫
        eqToHom (congrArg D.page hn.symm) := by
    subst n
    simp only [eqToHom_refl,Category.comp_id]
  refine ⟨z,?_⟩
  change (Subobject.ofLE (D.Z ⊤) (D.Z n₀) (D.Z_anti le_top) ≫ D.pageπ n₀) z=x
  rw [normalize n₀ hn₀]
  change (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0 ≫ e.hom) z=x
  have hz' := congrArg (fun y => e.hom y) hz
  simpa only [ModuleCat.comp_apply,show e.hom (e.inv x)=x from e.toLinearEquiv.apply_symm_apply x] using hz'


private theorem route_regrade_comp_zero_iff
    {m m' w w' : ℤ} {Y Z : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (b : BiHom m w Y) (f : Y ⟶ Z) :
    homotopyRegrade hm hw b ≫ f=0 ↔ b ≫ f=0 := by
  subst m'; subst w'; rfl

open CategoryTheory.Pretriangulated

private theorem route_invisible_lambda_kernel_nuzero
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj (nuZero model X)))
    (halambda : a ≫ SyntheticCategory.lam.app _ = 0)
    (haQ : ∀ n : ℕ, a ≫ (SyntheticCategory.biShift (0,-1)).map
      (XModLambdaN.incl (nuZero model X) n) = 0) : a=0 := by
  let V := nuZero model X
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hshift : F.map a ≫ F.map (lambdaPow 1 V) = 0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,halambda,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle V 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished V 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> dsimp <;> omega)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  let c : BiHom (m+1) w (XModLambdaN V 1) := eS.hom ≫ b
  have hboundary : c ≫ XModLambdaN.proj V 1 = eS.hom ≫ F.map a := by
    simpa [c,F,XModLambdaN.cofiberTriangle,Category.assoc] using
      congrArg (fun f => eS.hom ≫ f) hb.symm
  let s : ℤ := w-(m+1)
  let c' : BiHom (w-s) w (XModLambdaN V 1) := homotopyRegrade (by dsimp[s]; omega) rfl c
  obtain ⟨x,hx⟩ := Choice.nu_first_quotient_label_surjective X s w c'
  have hreach (n : ℕ) : ReachesPage
      (model.classical.obj (X.obj model.auxiliary)) ((n:ℤ)+2) (s,w) x := by
    cases n with
    | zero => simpa using (show ReachesPage _ 2 (s,w) x from ⟨x,RepresentsOnPage.self_two x⟩)
    | succ n =>
      let T := (model.quotients.tower V).triangle (by decide : 0<1)
        (show 1<n+2 by omega)
      have hproj : c' ≫ XModLambdaN.proj V 1 ≫
          F.map (G.map (XModLambdaN.incl V (n+2-1))) = 0 := by
        have h : c ≫ XModLambdaN.proj V 1 ≫
            F.map (G.map (XModLambdaN.incl V (n+2-1))) = 0 := by
          rw [←Category.assoc,hboundary,Category.assoc,←Functor.map_comp,haQ,Functor.map_zero,comp_zero]
        exact (route_regrade_comp_zero_iff (by dsimp[s]; omega) rfl c _).mpr h
      have hd : c' ≫ T.delta = 0 := by
        rw [Choice.lambda_zero_shift_delta_evaluation X 1 (n+2) (by decide) (by omega) (w-s) w c']
        exact hproj
      obtain ⟨d,hd⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₃ T.distinguished c' hd
      have hreach' := (KIP126.Literature.Standard.bhs_finite_lift X (n+2) (by omega) s w x).mpr
        ⟨d,by simpa only [T,Triangle.mk,(model.quotients.tower V).triangle_rho] using hd.symm.trans hx.symm⟩
      simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,add_assoc,Int.reduceAdd] using hreach'
  obtain ⟨z,hz⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s w x).mp
    (route_permanent_of_all_reaches X (s,w) x hreach)
  have hzero' : c' ≫ XModLambdaN.proj V 1 = 0 := by
    change z ≫ XModLambdaN.incl V 1 = firstLabel model X s w x at hz
    rw [←hx,←hz,Category.assoc,XModLambdaN.incl_comp_proj,comp_zero]
  have hzero : c ≫ XModLambdaN.proj V 1 = 0 := by
    exact (route_regrade_comp_zero_iff (by dsimp[s]; omega) rfl c _).mp hzero'
  have haz : F.map a = 0 := by
    apply (cancel_epi eS.hom).mp
    rw [←hboundary,hzero,comp_zero]
  exact F.map_injective (by simpa only [Functor.map_zero] using haz)


private theorem route_invisible_lambda_one_zero_nuzero
    (X : ClassicalObject) (m w : ℤ) (a : BiHom m w (nuZero model X))
    (halambda : lambdaMultiply 1 a=0)
    (haQ : ∀ n : ℕ, quotientClass n a=0) : a=0 := by
  let V := nuZero model X
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  letI : G.Additive := model.exactness.shiftAdditive (0,-1)
  let e : Smn (Syn:=SyntheticSpectrum) m (w-1) ≅ G.obj (Smn m w) :=
    eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
      ((SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0).symm
  let z : BiHom m (w-1) (G.obj V) := e.hom ≫ G.map a
  have hraw : SyntheticCategory.lam.app (Smn m w) ≫ a=0 := by
    simpa only [lambdaMultiply,lambdaPow_one model.quotients.coherence,
      comp_eq_zero_iff_of_epi] using halambda
  have hz : z ≫ SyntheticCategory.lam.app V=0 := by
    dsimp only [z]
    rw [Category.assoc,SyntheticCategory.lam.naturality]
    simp only [Functor.id_map,←Category.assoc,hraw,comp_zero]
  have hq (n : ℕ) : z ≫ G.map (XModLambdaN.incl V n)=0 := by
    dsimp only [z]
    rw [Category.assoc,←Functor.map_comp]
    change e.hom ≫ G.map (quotientClass n a)=0
    rw [haQ,Functor.map_zero,comp_zero]
  have hz0 := route_invisible_lambda_kernel_nuzero X m (w-1) z hz hq
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_injective
  apply (cancel_epi e.hom).mp
  simpa only [z,Functor.map_zero,comp_zero] using hz0

open KIP126.Main.Internal.Selected

private theorem route_invisible_lambda_torsion_zero_nuzero
    (X : ClassicalObject) (m w : ℤ) (a : BiHom m w (nuZero model X))
    (haQ : ∀ n : ℕ, quotientClass n a=0)
    (htorsion : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  obtain ⟨k,hk⟩ := htorsion
  induction k generalizing w with
  | zero =>
    simpa only [lambdaMultiply,lambdaPow,Category.assoc,comp_eq_zero_iff_of_epi] using hk
  | succ k ih =>
    let b := lambdaMultiply k a
    have hbQ (n : ℕ) : quotientClass n b=0 := by
      simpa only [quotientClass,b,lambdaMultiply,Category.assoc,comp_zero] using
        congrArg (fun z => lambdaMultiply k z) (haQ n)
    have hbOne : lambdaMultiply 1 b=0 := by
      have he := lambda_multiply_compose k 1 a
      rw [hk] at he
      have zero_heq (u v : ℤ) (h:u=v) :
          HEq (0:BiHom m u (nuZero model X)) (0:BiHom m v (nuZero model X)) := by
        subst v
        rfl
      exact eq_of_heq (he.trans (zero_heq _ _ (by omega)))
    have hb0 := route_invisible_lambda_one_zero_nuzero X m (w-k) b hbOne hbQ
    exact ih w a haQ hb0


private theorem nu_infinite_filtration_lambda_torsion_zero
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let e : nuZero model X ≅ V := SyntheticCategory.biShift_zero.app V
  let b : BiHom m w (nuZero model X) := a ≫ e.inv
  have haQ (n : ℕ) : quotientClass n a=0 := by
    apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated (.nu X) n m w
      (quotientClass n a)
    intro s
    exact KIP126.ProofTools.Internal.map_preserves_filtration
      (model.convergentMap (.nu X) (.quotient n (.nu X)) (XModLambdaN.incl V n))
      (m,w) s a (ha s)
  have hbQ (n : ℕ) : quotientClass n b=0 := by
    dsimp only [quotientClass,b]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    change quotientClass n a ≫ XModLambdaN.map e.inv n=0
    rw [haQ,zero_comp]
  have hbT : ∃ k : ℕ, lambdaMultiply k b=0 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    change lambdaMultiply k (a≫e.inv)=0
    have h := congrArg (fun z => z≫e.inv) hk
    simpa only [lambdaMultiply,Category.assoc,zero_comp] using h
  have hb0 := route_invisible_lambda_torsion_zero_nuzero X m w b hbQ hbT
  apply (cancel_mono e.inv).mp
  simpa only [b,zero_comp] using hb0

private theorem sphere_infinite_filtration_lambda_torsion_zero
    (m w : ℤ) (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  let b := a ≫ model.nu.unitIso.inv
  have hbF (s : ℕ) : FiltrationAtLeast model.syntheticTower s b :=
    KIP126.ProofTools.Internal.map_preserves_filtration
      (model.convergentMap .sphere (.nu .sphere) model.nu.unitIso.inv) (m,w) s a (ha s)
  have hbT : ∃ k : ℕ, lambdaMultiply k b=0 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    have h := congrArg (fun z => z≫model.nu.unitIso.inv) hk
    simpa only [b,lambdaMultiply,Category.assoc,zero_comp] using h
  have hb0 := nu_infinite_filtration_lambda_torsion_zero .sphere m w b hbF hbT
  apply (cancel_mono model.nu.unitIso.inv).mp
  simpa only [b,zero_comp] using hb0



/-- An infinitely filtered sphere class of order dividing two vanishes.
Finite λ quotient separation eliminates the λ-torsion kernel; finite-map
separation identifies the remaining realization as odd torsion. -/
private theorem sphere_infinite_two_torsion_zero (m w : ℤ)
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a)
    (h2 : a+a=0) : a=0 := by
  have hRzero : Standard.realizeSphere m w a=0 := by
    by_contra hne
    have hRtwo : Standard.realizeSphere m w a + Standard.realizeSphere m w a=0 := by
      rw [←map_add,h2,map_zero]
    exact (two_torsion_not_odd _ hRtwo hne) (infinite_realization_odd a ha)
  exact sphere_infinite_filtration_lambda_torsion_zero m w a ha
    ((Standard.selected_realization_kernel .sphere m w a).mp ((realize_zero_iff a).mp hRzero))

theorem synthetic_filtration26_zero (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 26 a) (h2 : a+a=0) : a=0 :=
  sphere_infinite_two_torsion_zero 125 130 a (synthetic_filtration26_infinite a ha) h2

end
end KIP126.Main.Internal.High125
