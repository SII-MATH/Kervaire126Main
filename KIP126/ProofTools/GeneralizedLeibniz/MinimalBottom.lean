module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite

/-! The minimal-length bottom crossing condition for the actual normalized map.
Source division uses a finite lambda quotient with zero high filtration. Its
image has the bottom filtration of a shifted nu object. No reflection of high
target filtration through lambda, and no paper GL theorem, is used. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private def bottomTranslate (A : SyntheticSpectrum) (δ : ℤ × ℤ) (m w : ℤ) :
    BiHom (m-δ.1) (w-δ.2) A ≃+
      BiHom m w ((SyntheticCategory.biShift δ).obj A) :=
  (suspInvarianceAddEquiv (m-δ.1) (w-δ.2) δ.1 δ.2 A).trans
    (regradeAddEquiv (sub_add_cancel m δ.1) (sub_add_cancel w δ.2))

private theorem bottom_translate_filtration_iff (A : SyntheticObject)
    (δ : ℤ × ℤ) (m w u : ℤ)
    (a : BiHom (m-δ.1) (w-δ.2) (A.obj model.nu model.auxiliary)) :
    FiltrationAtLeast model.syntheticTower u (bottomTranslate _ δ m w a) ↔
      FiltrationAtLeast model.syntheticTower u a := by
  change FiltrationAtLeast model.syntheticTower u
    (homotopyRegrade (sub_add_cancel m δ.1) (sub_add_cancel w δ.2)
      (susp_invariance (m-δ.1) (w-δ.2) δ.1 δ.2 _ a)) ↔ _
  rw [regrade_filtration_iff]
  have he : susp_invariance (m-δ.1) (w-δ.2) δ.1 δ.2 _ a =
      shiftHomotopyClass δ (m-δ.1,w-δ.2) a := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [he]
  exact shift_filtration_iff A δ (m-δ.1,w-δ.2) u a

private theorem bottom_translate_comp (A B : SyntheticSpectrum) (g : A ⟶ B)
    (δ : ℤ × ℤ) (m w : ℤ) (a : BiHom (m-δ.1) (w-δ.2) A) :
    bottomTranslate A δ m w a ≫ (SyntheticCategory.biShift δ).map g =
      bottomTranslate B δ m w (a≫g) := by
  simp [bottomTranslate,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,regrade_precomp,Functor.map_comp]

private theorem shifted_nu_bottom_filtration (X : ClassicalObject)
    (δ : ℤ × ℤ) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))) :
    FiltrationAtLeast model.syntheticTower (w-δ.2-(m-δ.1)) a := by
  let E := bottomTranslate (model.nu.functor.obj (X.obj model.auxiliary)) δ m w
  let b := E.symm a
  have hb : FiltrationAtLeast model.syntheticTower (w-δ.2-(m-δ.1)) b := by
    have h := nu_bottom_filtration X (w-δ.2-(m-δ.1)) (w-δ.2)
    have he : w-δ.2-(w-δ.2-(m-δ.1)) = m-δ.1 := by omega
    rw [he] at h
    exact h b
  have h := (bottom_translate_filtration_iff (.nu X) δ m w
    (w-δ.2-(m-δ.1)) b).mpr hb
  change FiltrationAtLeast model.syntheticTower _ (E (E.symm a)) at h
  simpa only [AddEquiv.apply_symm_apply] using h

private theorem normalized_nu_source_division (X : ClassicalObject)
    (e : ℤ) (i : ℕ) (hi : 0 < i) (m w u : ℤ)
    (hu : (i:ℤ) ≤ m+u-(w-e))
    (a : BiHom m w ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))),
      b ≫ lambdaPow i _ = a := by
  let A : SyntheticObject := .shift (0,e) (.nu X)
  let V := A.obj model.nu model.auxiliary
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨Q,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) i
    (model.nu.functor.obj (X.obj model.auxiliary))
  have hproj : FiltrationAtLeast model.syntheticTower u
      (a≫XModLambdaN.incl V i) :=
    map_preserves_filtration (model.convergentMap A (.quotient i A)
      (XModLambdaN.incl V i)) (m,w) u a ha
  have hQ : FiltrationAtLeast model.syntheticTower u (a≫XModLambdaN.incl V i≫Q.hom) := by
    change (a≫XModLambdaN.incl V i≫Q.hom) ∈ model.syntheticTower.filtrationSubmodule
      ((SyntheticObject.shift (0,e) (.quotient i (.nu X))).obj model.nu model.auxiliary) u (m,w)
    simpa only [Category.assoc] using map_preserves_filtration
      (model.convergentMap (.quotient i A) (.shift (0,e) (.quotient i (.nu X))) Q.hom)
      (m,w) u _ hproj
  have hz := shifted_finite_high_filtration_zero X i hi e m w u hu _ hQ
  have hrho : a≫XModLambdaN.incl V i=0 := by
    have he := congrArg (fun z => z≫Q.inv) hz
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,zero_comp] using he
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle V i).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished V i) a hrho
  exact ⟨b,hb.symm⟩

private theorem normalized_nu_image_filtration (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (m w u : ℤ)
    (a : BiHom m w ((extensionSourceObject model X Y f).obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    FiltrationAtLeast model.syntheticTower (u+normalizedExponent model.classicalTower f)
      (a≫(model.normalizedMap X Y f).map) := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let A := (extensionSourceObject model X Y f).obj model.nu model.auxiliary
  let B := model.nu.functor.obj (Y.obj model.auxiliary)
  by_cases hu : u ≤ w-m-e
  · have hbottom : FiltrationAtLeast model.syntheticTower (w-m)
        (a≫(model.normalizedMap X Y f).map) := by
      have h := nu_bottom_filtration Y (w-m) w
      have he : w-(w-m)=m := by omega
      rw [he] at h
      exact h _
    exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by dsimp [e] at hu; omega) hbottom
  · let i := (u-(w-m-e)).toNat
    have hi : 0 < i := by dsimp only [i]; omega
    have hiz : (i:ℤ)=u-(w-m-e) := Int.toNat_of_nonneg (by omega)
    obtain ⟨b,hb⟩ := normalized_nu_source_division X e i hi m w u (by omega) a ha
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let c := b≫F.map (model.normalizedMap X Y f).map
    have hc : FiltrationAtLeast model.syntheticTower (u+e) c := by
      have h := shifted_nu_bottom_filtration Y (0,-(i:ℤ)) m w c
      convert h using 1
      dsimp at *
      omega
    have heq : c≫lambdaPow i B = a≫(model.normalizedMap X Y f).map := by
      dsimp only [c]
      rw [Category.assoc,lambdaPow_naturality,←Category.assoc,hb]
    rw [←heq]
    exact map_preserves_filtration (model.convergentMap (.shift (0,-(i:ℤ)) (.nu Y)) (.nu Y)
      (lambdaPow i B)) (m,w) (u+e) c hc

private theorem shifted_normalized_nu_image_filtration (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (δ : ℤ × ℤ) (m w u : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj
      ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    FiltrationAtLeast model.syntheticTower (u+normalizedExponent model.classicalTower f)
      (a≫(SyntheticCategory.biShift δ).map (model.normalizedMap X Y f).map) := by
  let A := (extensionSourceObject model X Y f).obj model.nu model.auxiliary
  let E := bottomTranslate A δ m w
  let b := E.symm a
  have hb : FiltrationAtLeast model.syntheticTower u b :=
    (bottom_translate_filtration_iff (extensionSourceObject model X Y f) δ m w u b).mp
      (by
        change FiltrationAtLeast model.syntheticTower u (E (E.symm a))
        simpa only [AddEquiv.apply_symm_apply] using ha)
  have himage := normalized_nu_image_filtration X Y f (m-δ.1) (w-δ.2) u b hb
  have h := (bottom_translate_filtration_iff (.nu Y) δ m w
    (u+normalizedExponent model.classicalTower f) (b≫(model.normalizedMap X Y f).map)).mpr himage
  rw [←bottom_translate_comp] at h
  change FiltrationAtLeast model.syntheticTower _
    (E (E.symm a)≫(SyntheticCategory.biShift δ).map (model.normalizedMap X Y f).map) at h
  simpa only [AddEquiv.apply_symm_apply] using h

private theorem minimal_length_shifted_nu_tower_no_crossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (δ p : ℤ × ℤ) (s l : ℤ)
    (hl : l ≤ normalizedExponent model.classicalTower f) :
    TowerNoCrossing (model.convergentMap (.shift δ (extensionSourceObject model X Y f))
      (.shift δ (.nu Y)) ((SyntheticCategory.biShift δ).map (model.normalizedMap X Y f).map))
      p s l := by
  apply tower_no_crossing_of_correction
  intro u v hsu huv hvs a ha hfa
  refine ⟨a,ha,?_,?_⟩
  · simp only [sub_self]
    exact (model.syntheticTower.filtrationSubmodule _ _ _).zero_mem
  · have h := shifted_normalized_nu_image_filtration X Y f δ p.1 p.2 u a ha
    exact model.syntheticTower.filtrationSubmodule_antitone _ p (by omega) h

private theorem minimal_length_bottom_tower_no_crossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (page : ℕ) (r l s t : ℤ)
    (hl : l ≤ normalizedExponent model.classicalTower f) :
    TowerNoCrossing (model.convergentMap
      (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
      (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
      ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (model.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent model.classicalTower f) (s+r) l :=
  minimal_length_shifted_nu_tower_no_crossing X Y f _ _ _ _ hl

end
end KIP126.ProofTools.Internal.Leibniz
