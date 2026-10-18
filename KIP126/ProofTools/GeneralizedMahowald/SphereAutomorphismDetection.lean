module
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection
import all KIP126.ProofTools.GeneralizedLeibniz.SphereAutomorphisms

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

private theorem sphere_precomp_preserves_filtration
    {A : SyntheticSpectrum} (m w s : ℤ) (u : Smn (Syn:=SyntheticSpectrum) m w ⟶ Smn m w)
    (a : BiHom m w A) (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (u≫a) := by
  obtain ⟨b,hb⟩ := ha
  refine ⟨u≫b,?_⟩
  change (u≫b)≫(model.syntheticTower.tower A).projection s=u≫a
  change b≫(model.syntheticTower.tower A).projection s=a at hb
  rw [Category.assoc,hb]

private theorem sphere_automorphism_first_finite
    (X : ClassicalObject) (m w : ℤ) (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    u.hom≫a=a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let Q := XModLambdaN A 1
  have ha : FiltrationAtLeast model.syntheticTower (w-m) a := by
    have h := finite_bottom_filtration X 1 (by omega) (w-m) w
    rw [show w-(w-m)=m by omega] at h
    exact h a
  have hs : FiltrationAtLeast model.syntheticTower (w-m)
      (shiftHomotopyClass (0,-1) (m,w) a) :=
    (shift_filtration_iff (.quotient 1 (.nu X)) (0,-1) (m,w) (w-m) a).mpr ha
  have hl : FiltrationAtLeast model.syntheticTower (w-m)
      (shiftHomotopyClass (0,-1) (m,w) a ≫ lambdaPow 1 Q) :=
    map_preserves_filtration
    (model.convergentMap (.shift (0,-1) (.quotient 1 (.nu X))) (.quotient 1 (.nu X))
      (lambdaPow 1 Q)) ((m,w)+(0,-1)) (w-m) (shiftHomotopyClass (0,-1) (m,w) a) hs
  have hz : shiftHomotopyClass (0,-1) (m,w) a≫lambdaPow 1 Q=0 :=
    finite_high_filtration_zero X 1 (by omega) ((m,w)+(0,-1)).1 ((m,w)+(0,-1)).2 (w-m)
      (by dsimp; omega) _ hl
  have hzero : lambdaPow 1 (Smn m w)≫a=0 := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0)).mp
    rw [comp_zero]
    erw [←lambdaPow_naturality]
    change ((SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
      (SyntheticCategory.biShift (0,-1)).map a ≫ lambdaPow 1 Q=0
    simpa only [shiftHomotopyClass,Category.assoc] using hz
  obtain ⟨b,hb⟩ := Triangle.yoneda_exact₂ (XModLambdaN.cofiberTriangle (Smn m w) 1)
    (XModLambdaN.cofiberTriangle_distinguished (Smn m w) 1) a hzero
  change a=XModLambdaN.incl (Smn m w) 1≫b at hb
  rw [hb,←Category.assoc,bigraded_sphere_automorphism_first_quotient]

private theorem finite_lambda_precomp_sphere
    (X : ClassicalObject) (q d : ℕ) (hd : 0<d) (hdq : d<q) (s t : ℤ)
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-d) ≅ Smn (t-s) (t-d))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    ∃ v : Smn (Syn:=SyntheticSpectrum) (t-s) t ≅ Smn (t-s) t,
      u.hom ≫ finiteLambdaClass X q d hd hdq s t b =
        finiteLambdaClass X q d hd hdq s t (v.hom≫b) := by
  let C := (biShiftAddIso (t-s,t) (0,-(d:ℤ)) (t-s,t-d) (by ext <;> simp [sub_eq_add_neg])).app
    (S_0_0 : SyntheticSpectrum)
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  let v : Smn (t-s) t ≅ Smn (t-s) t := ff.preimageIso (C ≪≫ u ≪≫ C.symm)
  refine ⟨v,?_⟩
  unfold finiteLambdaClass
  rw [shift_regrade,shift_regrade]
  simp only [Category.assoc]
  change u.hom ≫ (C.inv ≫ (SyntheticCategory.biShift (0,-(d:ℤ))).map b ≫ _) =
    C.inv ≫ (SyntheticCategory.biShift (0,-(d:ℤ))).map (v.hom≫b) ≫ _
  have hv : (SyntheticCategory.biShift (0,-(d:ℤ))).map v.hom = C.hom≫u.hom≫C.inv :=
    ff.map_preimage _
  simp only [Functor.map_comp,hv,Category.assoc,Iso.inv_hom_id_assoc]

private theorem sphere_automorphism_finite_positive_detects
    (X : ClassicalObject) (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-k) ≅ Smn (t-s) (t-k))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (u.hom≫a) := by
  obtain ⟨b,hb⟩ := finite_detected_target_bottom_lift X q k hkq s t x a ha
  obtain ⟨v,hv⟩ := finite_lambda_precomp_sphere X q k hk hkq s t u b
  have hb' : (v.hom≫b) ≫ (model.quotients.tower _).rho 1 (q-k) (by omega) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [Category.assoc,sphere_automorphism_first_finite,hb]
  have hgood := finite_quotient_lambda_detects X q k hk hkq s t x (v.hom≫b) hb'
  rw [←hv] at hgood
  have hbase := finite_quotient_lambda_detects X q k hk hkq s t x b hb
  have hdiff := detects_sub_filtration (model.convergence (.quotient q (.nu X))) (s,t,t-k) ha hbase
  have hu := sphere_precomp_preserves_filtration (t-s) (t-k) (s+1) u.hom _ hdiff
  rw [Preadditive.comp_sub] at hu
  exact detects_of_high_difference (.quotient q (.nu X)) (s,t,t-k) _ _ _ hgood hu

private theorem sphere_automorphism_finite_bottom_detects
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : (model.family.obj ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary)).E₂ (s,t,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) t ≅ Smn (t-s) t)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t) x a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t) x (u.hom≫a) := by
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X q hq s t a
  have hx1 : (u.hom≫a) ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x0 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [Category.assoc,sphere_automorphism_first_finite,hx0]
  have h0 := first_label_detects_unshifted X q hq s t x0 a hx0
  have h1 := first_label_detects_unshifted X q hq s t x0 (u.hom≫a) hx1
  exact detects_of_high_difference (.quotient q (.nu X)) (s,t,t) x _ _ ha
    (detects_sub_filtration (model.convergence (.quotient q (.nu X))) (s,t,t) h1 h0)

private theorem sphere_automorphism_finite_detects
    (X : ClassicalObject) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-k) ≅ Smn (t-s) (t-k))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (u.hom≫a) := by
  by_cases hk : k=0
  · subst k
    have bottom (w : ℤ) (hw : w=t)
        (z : (model.family.obj ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary)).E₂ (s,t,w))
        (v : Smn (Syn:=SyntheticSpectrum) (t-s) w ≅ Smn (t-s) w)
        (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
        (hb : Detects (model.convergence (.quotient q (.nu X))) (s,t,w) z b) :
        Detects (model.convergence (.quotient q (.nu X))) (s,t,w) z (v.hom≫b) := by
      subst w
      exact sphere_automorphism_finite_bottom_detects X q hkq s t z v b hb
    exact bottom _ (by simp) _ u a ha
  · exact sphere_automorphism_finite_positive_detects X q k (by omega) hkq s t x u a ha

private theorem quotient_unshift_natural_automorphism_detects
    (X : ClassicalObject) (δ : ℤ×ℤ) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (η : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ ≅ SyntheticCategory.biShift δ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q≫ε.hom=(SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t-k)+δ).1 ((t-s,t-k)+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (quotientUnshift X δ (t-s,t-k) q ε a)) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X δ (t-s,t-k) q ε (a≫XModLambdaN.map (η.hom.app _) q)) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let Q := XModLambdaN A q
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let M : Q⟶Q := ff.preimage (ε.inv≫XModLambdaN.map (η.hom.app A) q≫ε.hom)
  let N : Q⟶Q := ff.preimage (η.hom.app Q)
  have hM : F.map M=ε.inv≫XModLambdaN.map (η.hom.app A) q≫ε.hom := ff.map_preimage _
  have hN : F.map N=η.hom.app Q := ff.map_preimage _
  dsimp only [F] at hM hN
  have hbase : XModLambdaN.incl A q≫M=XModLambdaN.incl A q≫N := by
    apply ff.map_injective
    simp only [Functor.map_comp,hM,hN]
    rw [←hε,Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hε]
    exact (η.hom.naturality (XModLambdaN.incl A q)).symm
  let b := quotientUnshift X δ (t-s,t-k) q ε a
  have he : quotientUnshift X δ (t-s,t-k) q ε (a≫XModLambdaN.map (η.hom.app A) q)=b≫M := by
    apply ff.map_injective
    simp only [quotientUnshift,b,Functor.map_comp,Functor.FullyFaithful.map_preimage,hM,Category.assoc,
      Iso.hom_inv_id_assoc]
  have hm := quotient_nu_maps_equal_on_spheres X X q (by omega) M N hbase (t-s) (t-k) b
  let u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-k) ≅ Smn (t-s) (t-k) :=
    ff.preimageIso (η.app _)
  have hn : b≫N=u.hom≫b := by
    apply ff.map_injective
    simp only [Functor.map_comp,hN,u,Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
    exact η.hom.naturality b
  rw [he,hm,hn]
  exact sphere_automorphism_finite_detects X q k hkq s t x u b ha

end
end KIP126.ProofTools.Internal.Mahowald
