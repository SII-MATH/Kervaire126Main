module
public import KIP126.Main.Conditions
/-! Fixed λ-calculus from Selected/DetectionData.lean:230–430 at bbac1fc05843
(MIT). These are proved operations on the existing shift and quotient data. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private theorem shift_assoc_inv (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : SyntheticSpectrum) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private def push3 {m w : ℤ} {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-3) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-3)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-3)).map a ≫ f


private theorem eta_push3 {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (x : BiHom 124 134 X) :
    sphereAction ν (push3 f x) = push3 f (sphereAction ν x) := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,134) (0,-3)
    (125,136) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  simp only [push3, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,131)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (124,131)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (0,-3)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-3)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : SyntheticSpectrum) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem eta_lambda3_right
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) :
    sphereProduct η (lambdaMultiply 3 u)=lambdaMultiply 3 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
      push3 (lambdaPow 3 (S_0_0 : SyntheticSpectrum)) a=lambdaMultiply 3 a := by
    simp only [push3,lambdaMultiply]
    erw [lambdaPow_naturality]
    rfl
  have h := eta_push3 (lambdaPow 3 (S_0_0 : SyntheticSpectrum)) η u
  rw [heq,heq] at h
  exact h


private def push6 {m w : ℤ} {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-6) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-6)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-6)).map a ≫ f


private theorem eta_push6 {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (x : BiHom 124 134 X) :
    sphereAction ν (push6 f x) = push6 f (sphereAction ν x) := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,134) (0,-6)
    (125,136) (124,128) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  simp only [push6, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,128)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (124,128)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (0,-6)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-6)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-6)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : SyntheticSpectrum) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem eta_lambda6_right
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) :
    sphereProduct η (lambdaMultiply 6 u)=lambdaMultiply 6 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
      push6 (lambdaPow 6 (S_0_0 : SyntheticSpectrum)) a=lambdaMultiply 6 a := by
    simp only [push6,lambdaMultiply]
    erw [lambdaPow_naturality]
    rfl
  have h := eta_push6 (lambdaPow 6 (S_0_0 : SyntheticSpectrum)) η u
  rw [heq,heq] at h
  exact h


private theorem lambda_three_3_136
    (c : BiHom 125 136 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 3 (lambdaMultiply 3 c)=lambdaMultiply 6 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (125,136) (0,-3) (0,-3)
    (125,133) (0,-6) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 3 (Smn 125 136)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add model.quotients.coherence 3 3 6 (by decide) (Smn 125 136)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem lambda_three_7_140
    (c : BiHom 125 140 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 3 (lambdaMultiply 7 c)=lambdaMultiply 10 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (125,140) (0,-7) (0,-3)
    (125,133) (0,-10) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,140) (0,-7)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 7 (Smn 125 140)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add model.quotients.coherence 7 3 10 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem lambda_three_6_139
    (c : BiHom 125 139 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 3 (lambdaMultiply 6 c)=lambdaMultiply 9 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (125,139) (0,-6) (0,-3)
    (125,133) (0,-9) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,139) (0,-6)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 6 (Smn 125 139)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add model.quotients.coherence 6 3 9 (by decide) (Smn 125 139)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private abbrev VanishesModLambda {m w : ℤ} {X : SyntheticSpectrum}
    (n : ℕ) (a : BiHom m w X) : Prop := quotientClass n a = 0

private theorem vanishesModLambda_iff_factors {m n : ℤ} {X : SyntheticSpectrum} (r : ℕ)
    (x : BiHom m n X) :
    VanishesModLambda r x ↔
      ∃ y : Smn m n ⟶ (SyntheticCategory.biShift (0, -(r : ℤ))).obj X,
        y ≫ lambdaPow r X = x := by
  let T := XModLambdaN.cofiberTriangle X r
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := T.coyoneda_exact₂ hT x hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    change (y ≫ lambdaPow r X) ≫ XModLambdaN.incl X r = 0
    rw [Category.assoc,XModLambdaN.lambdaPow_comp_incl,Limits.comp_zero]

private theorem vanishes_mod_lambda_iff_multiple
    (n : ℕ) {X : SyntheticSpectrum} (m w : ℤ) (z : BiHom m (w-(n:ℤ)) X) :
    VanishesModLambda n z ↔ ∃ b : BiHom m w X, lambdaMultiply n b=z := by
  classical
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(n:ℤ))
  let e : F.obj (Smn m w : SyntheticSpectrum) ≅ Smn m (w-(n:ℤ)) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  have he (b : BiHom m w X) : lambdaMultiply n b=e.inv≫F.map b≫lambdaPow n X := by
    have he' : lambdaMultiply n b=e.inv≫lambdaPow n (Smn m w)≫b := by
      unfold lambdaMultiply
      change eqToHom (by congr 1; simp) ≫
        (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0 ≫
        lambdaPow n (Smn m w) ≫ b =
        (eqToHom (by congr 1; simp) ≫
          (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0) ≫
        lambdaPow n (Smn m w) ≫ b
      exact (Category.assoc _ _ _).symm
    rw [he',←lambdaPow_naturality n b]
  constructor
  · intro hz
    obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors n z).mp hz
    let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-(n:ℤ))).preimage (e.hom≫a)
    have hb : F.map b=e.hom≫a :=
      (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-(n:ℤ))).map_preimage _
    refine ⟨b,?_⟩
    rw [he,hb]
    simp only [Category.assoc,e.inv_hom_id_assoc]
    exact ha
  · rintro ⟨b,rfl⟩
    apply (vanishesModLambda_iff_factors n (lambdaMultiply n b)).mpr
    exact ⟨e.inv≫F.map b,by rw [Category.assoc,←he]⟩


private theorem map_filtration (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    {m w s : ℤ} (a : BiHom m w (A.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (a ≫ f) := by
  let M := model.convergentMap A B f
  let FA := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  let FB := model.syntheticTower.filtration (B.obj model.nu model.auxiliary)
  have ham : a ∈ ModuleCat.subobjectModule (syntheticHomotopy
      (A.obj model.nu model.auxiliary) (m,w)) (FA.F s (m,w)) := by
    simpa only [FA,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  have hb : a ≫ f ∈ ModuleCat.subobjectModule (syntheticHomotopy
      (B.obj model.nu model.auxiliary) (m,w)) (FB.F s (m,w)) := by
    refine ⟨(M.filteredMap.compat s (m,w)).choose a',?_⟩
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat s (m,w)).choose_spec a'
    have hf := ConcreteCategory.congr_hom (M.filteredMap_map (m,w)) ((FA.F s (m,w)).arrow a')
    change M.filteredMap.map (m,w) ((FA.F s (m,w)).arrow a') = (FA.F s (m,w)).arrow a' ≫ f at hf
    change (FB.F s (m,w)).arrow ((M.filteredMap.compat s (m,w)).choose a') =
      M.filteredMap.map (m,w) ((FA.F s (m,w)).arrow a') at h
    exact h.trans (hf.trans (congrArg (fun z => z ≫ f) ha'))
  simpa only [FB,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hb

private theorem lambda_9_iff_filtration_14
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum)) :
    VanishesModLambda 9 a ↔ FiltrationAtLeast model.syntheticTower 14 a := by
  classical
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 125 130 14 (by omega) (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 14 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 139 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 9 b=a ≫ model.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (vanishes_mod_lambda_iff_multiple 9 125 139 a).mp hz
    have haν := h.mpr ⟨b ≫ model.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ model.nu.unitIso.inv) hb)⟩
    have hm := map_filtration (.nu .sphere) .sphere model.nu.unitIso.hom (a ≫ model.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha)
    apply (vanishes_mod_lambda_iff_multiple 9 125 139 a).mpr
    refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ model.nu.unitIso.hom) hb


private theorem lambda_10_iff_filtration_15
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum)) :
    VanishesModLambda 10 a ↔ FiltrationAtLeast model.syntheticTower 15 a := by
  classical
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 125 130 15 (by omega) (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 15 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ model.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (vanishes_mod_lambda_iff_multiple 10 125 140 a).mp hz
    have haν := h.mpr ⟨b ≫ model.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ model.nu.unitIso.inv) hb)⟩
    have hm := map_filtration (.nu .sphere) .sphere model.nu.unitIso.hom (a ≫ model.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha)
    apply (vanishes_mod_lambda_iff_multiple 10 125 140 a).mpr
    refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ model.nu.unitIso.hom) hb

private theorem lambda_three_preserves_filtration_fifteen
    (a : BiHom 125 133 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 15 a) :
    FiltrationAtLeast model.syntheticTower 15 (lambdaMultiply 3 a) := by
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 125 133 15 (by omega) (a≫model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 15 (a≫model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (model.nu.functor.obj SphereSpectrum),lambdaMultiply 7 b=a≫model.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha)
  let c : BiHom 125 140 (S_0_0 : SyntheticSpectrum) := b≫model.nu.unitIso.hom
  have hc : lambdaMultiply 7 c=a := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z≫model.nu.unitIso.hom) hb
  apply (lambda_10_iff_filtration_15 _).mp
  apply (vanishes_mod_lambda_iff_multiple 10 125 140 _).mpr
  exact ⟨c,by rw [←hc,lambda_three_7_140 c]⟩

end
end KIP126.Main.Internal.Selected
