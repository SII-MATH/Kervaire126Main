module
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection

/-! Actual left-edge representatives for AimPaper Theorem 6.1. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 800000
set_option Elab.async false

set_option backward.defeqAttrib.useBackward true

private theorem normalized_regrade_trans {A : SyntheticAdamsSS} {i j k : Tridegree}
    (hij : i=j) (hjk : j=k) (x : A.E₂ i) :
    regradeE2 hjk (regradeE2 hij x)=regradeE2 (hij.trans hjk) x := by
  subst j; subst k; rfl

private theorem normalized_homotopy_regrade_trans {A : SyntheticSpectrum}
    {m m' m'' w w' w'' : ℤ} (hm : m=m') (hm' : m'=m'')
    (hw : w=w') (hw' : w'=w'') (a : BiHom m w A) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a)=
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'; subst m''; subst w'; subst w''; rfl

private theorem shifted_nu_source_first
    (X : ClassicalObject) (e s t : ℤ) (he : e=0 ∨ e=1)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.shift ((0:ℤ),e) (.nu X))) (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x))
      (homotopyRegrade (by simp) rfl (shiftHomotopyClass ((0:ℤ),e) (t-s,t) a))) :
    a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hm := detects_map (.shift ((0:ℤ),e) (.nu X)) (.quotient 1 (.shift ((0:ℤ),e) (.nu X)))
    (XModLambdaN.incl _ 1) (s,t,t+e) _ _ ha
  rw [←page_regrade] at hm
  change Detects (model.convergence (.quotient 1 (.shift ((0:ℤ),e) (.nu X)))) (s,t,t+e)
    (regradeE2 _ (finiteNuLabel model X 1 e s t 0 x)) _ at hm
  have hf := shifted_finite_source_first X 1 (by decide) e s t x _ hm
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hf
  rcases he with rfl | rfl
  · have hh := (zero_finite_source_desuspend X 1 (by decide) s t x _ hm).1
    simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hh
    dsimp only [SyntheticObject.obj] at hh
    rw [regrade_comp,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc] at hh
    have hz : homotopyRegrade rfl (show t+0=t by omega)
        (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,0) (t-s,t) a)) ≫
        SyntheticCategory.biShift_zero.hom.app _ = a := by
      simpa only [regrade_precomp,←Category.assoc,eqToHom_trans,lambdaPow] using
        shift_zero_lambda _ (t-s,t) a
    rw [hz] at hh
    exact hh
  · letI := model.exactness.shiftCommShift (0,1)
    letI := model.exactness.shiftExact (0,1)
    obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
      (model.nu.functor.obj (X.obj model.auxiliary))
    have hh := congrArg (fun z => quotientUnshift X (0,1) (t-s,t) 1 ε
      (homotopyRegrade (by simp) rfl z)) hf
    rw [positive_first_desuspend X s t x ε hε] at hh
    convert hh using 1
    rw [regrade_comp,homotopy_regrade_inverse]
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,1)).map_injective
    simp only [quotientUnshift,Functor.FullyFaithful.map_preimage,Functor.map_comp,
      Category.assoc]
    dsimp only [SyntheticObject.obj]
    rw [hε]
    simp [shiftHomotopyClass,Category.assoc]


set_option backward.defeqAttrib.useBackward false in
private theorem normalized_source_infinity_shift
    (X : ClassicalObject) (e s t : ℤ) (he : e=0 ∨ e=1)
    (x : Ambient model X (s,t))
    (z : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData
      (s,t,t)).eInfty)
    (hz : HasInfinityRepresentative _ 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) z)
    (zN : ((model.family.obj ((SyntheticObject.shift ((0:ℤ),e) (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s,((t-s,t)+((0:ℤ),e)).1+s,((t-s,t)+((0:ℤ),e)).2)).eInfty)
    (hzN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> simp) (model.comparison.nuE2 X e s t 0 x)) zN) :
    (towerInfinityIso (model.convergence (.nu X)) (model.convergence (.shift ((0:ℤ),e) (.nu X)))
      ((essShift ((0:ℤ),e)).filtered (.nu X) (t-s,t)) s).hom
      ((eqToHom (congrArg (fun i => ((model.family.obj
        (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData i).eInfty)
          (show (s,t,t)=(s,(t-s)+s,t) by simp))) z) = zN := by
  let p : ℤ×ℤ := (t-s,t)
  let δ : ℤ×ℤ := ((0:ℤ),e)
  let F := model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))
  let I := towerInfinityIso (model.convergence (.nu X))
    (model.convergence (.shift δ (.nu X))) ((essShift δ).filtered (.nu X) p) s
  let z₀ := I.inv zN
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence (.nu X)) p s).hom z₀)
  obtain ⟨b,hb,hgb⟩ := shift_frame (.nu X) δ p s z₀ a ha
  have hIz : I.hom z₀ = zN := I.toLinearEquiv.apply_symm_apply zN
  rw [hIz] at hgb
  have hbd := source_frame_detects (model.convergence (.shift δ (.nu X)))
    (p+δ) s zN _ hzN b hgb
  rw [hb] at hbd
  have hind : (s,(p+δ).1+s,(p+δ).2)=(s,t,t+e) := by
    ext <;> dsimp [p,δ] <;> omega
  have hbd := detects_transport hind _ _ hbd
  have hbstd : Detects (model.convergence (.shift ((0:ℤ),e) (.nu X))) (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x))
      (homotopyRegrade (by simp) rfl
        (shiftHomotopyClass ((0:ℤ),e) (t-s,t) ((F.F s p).arrow a))) := by
    convert hbd using 1
    · simp only [normalized_regrade_trans]
    · simp only [normalized_homotopy_regrade_trans]
      rfl
  have hfirst := shifted_nu_source_first X e s t he x ((F.F s p).arrow a) hbstd
  have hx := ((KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x z).mp hz).1
  have had := nu_first_label_detects X s t x hx ((F.F s p).arrow a) hfirst
  have hind₀ : (s,t,t)=(s,p.1+s,p.2) := by simp [p]
  have had := detects_transport hind₀ _ _ had
  have hastem : Detects (model.convergence (.nu X)) (s,p.1+s,p.2)
      (regradeE2 hind₀ (nuWeightLabel model X s t t (by omega) x))
      (homotopyRegrade (by dsimp; omega) rfl ((F.F s p).arrow a)) := by
    convert had using 1
  obtain ⟨z₁,hz₁,a₁,ha₁,hga₁⟩ := frame_of_source_detects (model.convergence (.nu X))
    p s _ ((F.F s p).arrow a) hastem
  have haeq : a₁=a := (ModuleCat.mono_iff_injective (F.F s p).arrow).mp inferInstance ha₁
  subst a₁
  have heq : z₀=z₁ := (infinityGradedIso (model.convergence (.nu X)) p s).toLinearEquiv.injective
    (ha.symm.trans hga₁)
  have hzstem := representative_transport hind₀ _ _ hz
  have hz₁eq := hz₁.unique hzstem
  change I.hom _=zN
  rw [←hz₁eq,←heq]
  exact hIz


private theorem zero_quotient_shift_unit
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift (0,0)).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    a ≫ ε.hom ≫ SyntheticCategory.biShift_zero.hom.app _ =
      a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let Z := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,0)
  let g := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q ≫
    SyntheticCategory.biShift_zero.inv.app (XModLambdaN A q)
  have hg : XModLambdaN.incl (Z.obj A) q ≫ g = Z.map (XModLambdaN.incl A q) := by
    dsimp only [g,Z]
    rw [←Category.assoc,←XModLambdaN.incl_naturality]
    have hn := SyntheticCategory.biShift_zero.hom.naturality (XModLambdaN.incl A q)
    dsimp only [Functor.id_map] at hn
    dsimp only [Functor.id_obj]
    rw [←hn,Category.assoc,Iso.hom_inv_id_app,Category.comp_id]
  have hh := shifted_quotient_sphere_congruence X X (0,0) q q hq le_rfl ε hε
    ε.hom g (hε.trans hg.symm) m w a
  have hh := congrArg (fun z => z ≫ SyntheticCategory.biShift_zero.hom.app (XModLambdaN A q)) hh
  simpa only [g,Category.assoc,Iso.inv_hom_id_app,Functor.id_obj,Category.comp_id] using hh

private theorem finite_shift_source_reflect
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (e s t : ℤ) (he : e=0 ∨ e=1)
    (ε : XModLambdaN ((SyntheticCategory.biShift ((0:ℤ),e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift ((0:ℤ),e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift ((0:ℤ),e)).map (XModLambdaN.incl _ q))
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.shift ((0:ℤ),e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x))
      (homotopyRegrade (by simp) rfl (shiftHomotopyClass ((0:ℤ),e) (t-s,t) a) ≫ ε.inv)) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a := by
  rcases he with rfl | rfl
  · have hd := (zero_finite_source_desuspend X q hq s t x _ ha).2
    have hu := zero_quotient_shift_unit X q hq ε hε (t-s) (t+0)
      (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,0) (t-s,t) a) ≫ ε.inv)
    simp only [Category.assoc,Iso.inv_hom_id_assoc] at hu
    have hu := congrArg (homotopyRegrade rfl (show t+0=t by omega)) hu
    simp only [regrade_comp] at hu
    have hz : homotopyRegrade rfl (show t+0=t by omega)
        (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,0) (t-s,t) a)) ≫
        SyntheticCategory.biShift_zero.hom.app _ = a := by
      simpa only [regrade_precomp,←Category.assoc,eqToHom_trans,lambdaPow] using
        shift_zero_lambda _ (t-s,t) a
    rw [hz] at hu
    rw [regrade_comp,Category.assoc] at hd
    rw [←hu] at hd
    exact hd
  · letI := model.exactness.shiftCommShift (0,1)
    letI := model.exactness.shiftExact (0,1)
    obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
      (model.nu.functor.obj (X.obj model.auxiliary))
    have hd := (positive_finite_source_desuspend X q hq s t x ε₁ ε hε₁ hε _ ha).2
    rw [regrade_comp,homotopy_regrade_inverse,quotient_unshift_shift] at hd
    exact hd


set_option backward.defeqAttrib.useBackward false in
private theorem normalized_finite_source_infinity_shift
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (e s t : ℤ) (he : e=0 ∨ e=1)
    (ε : XModLambdaN ((SyntheticCategory.biShift ((0:ℤ),e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift ((0:ℤ),e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift ((0:ℤ),e)).map (XModLambdaN.incl _ q))
    (x : Ambient model X (s,t))
    (z : ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)).sequence.ssData
      (s,t,t)).eInfty)
    (hz : HasInfinityRepresentative _ 2 (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) z)
    (zN : ((model.family.obj ((SyntheticObject.quotient q (.shift ((0:ℤ),e) (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData
      (s,((t-s,t)+((0:ℤ),e)).1+s,((t-s,t)+((0:ℤ),e)).2)).eInfty)
    (hzN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> simp) (finiteNuLabel model X q e s t 0 x)) zN) :
    (model.family.map ε.inv).eInftyMap
      (s,((t-s,t)+((0:ℤ),e)).1+s,((t-s,t)+((0:ℤ),e)).2)
      ((towerInfinityIso (model.convergence (.quotient q (.nu X)))
        (model.convergence (.shift ((0:ℤ),e) (.quotient q (.nu X))))
        ((essShift ((0:ℤ),e)).filtered (.quotient q (.nu X)) (t-s,t)) s).hom
        ((eqToHom (congrArg (fun i => ((model.family.obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)).sequence.ssData i).eInfty)
            (show (s,t,t)=(s,(t-s)+s,t) by simp))) z)) = zN := by
  let p : ℤ×ℤ := (t-s,t)
  let δ : ℤ×ℤ := (0,e)
  let A : SyntheticObject := .quotient q (.nu X)
  let B : SyntheticObject := .quotient q (.shift δ (.nu X))
  let F := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  let I := towerInfinityIso (model.convergence A)
    (model.convergence (.shift δ A)) ((essShift δ).filtered A p) s
  let zS := (model.family.map ε.hom).eInftyMap (s,(p+δ).1+s,(p+δ).2) zN
  let z₀ := I.inv zS
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence A) p s).hom z₀)
  obtain ⟨b,hb,hgb⟩ := shift_frame A δ p s z₀ a ha
  have hIz : I.hom z₀ = zS := I.toLinearEquiv.apply_symm_apply zS
  rw [hIz] at hgb
  have hMap : (model.family.map ε.inv).eInftyMap (s,(p+δ).1+s,(p+δ).2) zS = zN := by
    simp only [zS,←ModuleCat.comp_apply,←SpectralSequenceMorphism.eInftyMap_comp,
      ←SyntheticAdamsFamily.map_comp,Iso.hom_inv_id,SyntheticAdamsFamily.map_id,
      SpectralSequenceMorphism.eInftyMap_id,ConcreteCategory.id_apply]
  obtain ⟨c,hc,hgc⟩ := tower_map_frame (model.convergentMap (.shift δ A) B ε.inv)
    (p+δ) s zS b hgb
  have hgc' := hgc.trans (congrArg ((infinityGradedIso (model.convergence B) (p+δ) s).hom) hMap)
  have hcd := source_frame_detects (model.convergence B) (p+δ) s zN _ hzN c hgc'
  rw [←hc,hb] at hcd
  have hind : (s,(p+δ).1+s,(p+δ).2)=(s,t,t+e) := by
    ext <;> dsimp [p,δ] <;> omega
  have hcd := detects_transport hind _ _ hcd
  have hcstd : Detects (model.convergence (.quotient q (.shift ((0:ℤ),e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x))
      (homotopyRegrade (by simp) rfl
        (shiftHomotopyClass ((0:ℤ),e) (t-s,t) ((F.F s p).arrow a)) ≫ ε.inv) := by
    convert hcd using 1
    · simp only [normalized_regrade_trans]
    · simp only [normalized_homotopy_regrade_trans,regrade_comp]
      rfl
  have had := finite_shift_source_reflect X q hq e s t he ε hε x ((F.F s p).arrow a) hcstd
  have hind₀ : (s,t,t)=(s,p.1+s,p.2) := by simp [p]
  have had := detects_transport hind₀ _ _ had
  have hastem : Detects (model.convergence A) (s,p.1+s,p.2)
      (regradeE2 hind₀ (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)))
      (homotopyRegrade (by dsimp; omega) rfl ((F.F s p).arrow a)) := by
    convert had using 1
  obtain ⟨z₁,hz₁,a₁,ha₁,hga₁⟩ := frame_of_source_detects (model.convergence A)
    p s _ ((F.F s p).arrow a) hastem
  have haeq : a₁=a := (ModuleCat.mono_iff_injective (F.F s p).arrow).mp inferInstance ha₁
  subst a₁
  have heq : z₀=z₁ := (infinityGradedIso (model.convergence A) p s).toLinearEquiv.injective
    (ha.symm.trans hga₁)
  have hzstem := representative_transport hind₀ _ _ hz
  have hz₁eq := hz₁.unique hzstem
  change (model.family.map ε.inv).eInftyMap _ (I.hom _)=zN
  exact (congrArg (fun v => (model.family.map ε.inv).eInftyMap
    (s,(p+δ).1+s,(p+δ).2) (I.hom v)) (heq.trans hz₁eq).symm).trans
      ((congrArg ((model.family.map ε.inv).eInftyMap (s,(p+δ).1+s,(p+δ).2)) hIz).trans hMap)


private theorem sphere_automorphism_nu_target_detects
    (X : ClassicalObject) (k : ℕ) (s t : ℤ)
    (x : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-k) ≅ Smn (t-s) (t-k))
    (a : BiHom (t-s) (t-k) (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,t-k)
      (targetNuLabel model X s t k x) a) :
    Detects (model.convergence (.nu X)) (s,t,t-k)
      (targetNuLabel model X s t k x) (u.hom≫a) := by
  let q := k+1
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hmap := detects_map (.nu X) (.quotient q (.nu X))
    (XModLambdaN.incl A q) (s,t,t-k) _ a ha
  have hfinite : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (a≫XModLambdaN.incl A q) := hmap
  have hu := sphere_automorphism_finite_detects X q k (by dsimp [q]; omega)
    s t x u (a≫XModLambdaN.incl A q) hfinite
  have hfil := sphere_precomp_preserves_filtration (t-s) (t-k) s u.hom a
    (detects_filtration (.nu X) (s,t,t-k) _ a ha)
  obtain ⟨e,he,_⟩ := ha
  apply detects_reflect (.nu X) (.quotient q (.nu X))
    (XModLambdaN.incl A q) (s,t,t-k)
    (nu_projection_infinity_injective X q (by dsimp [q]; omega)
      s t (t-k) (by dsimp [q]; omega)) _ e he (u.hom≫a) hfil
  rw [Category.assoc]
  exact hu

private theorem sphere_automorphism_nu_detects
    (X : ClassicalObject) (s t w : ℤ) (hw : w≤t)
    (x : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) w ≅ Smn (t-s) w)
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) a) :
    Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) (u.hom≫a) := by
  generalize hk : (t-w).toNat=k at *
  have hw' : w=t-k := by omega
  subst w
  have hlabel : nuWeightLabel model X s t (t-k) hw x = targetNuLabel model X s t k x := by
    unfold nuWeightLabel
    have labels (j : ℕ) (hj : j=k) (h : (s,t,t-j)=(s,t,t-k)) :
        regradeE2 h (targetNuLabel model X s t j x) = targetNuLabel model X s t k x := by
      subst j
      rfl
    exact labels _ hk _
  rw [hlabel] at ha ⊢
  exact sphere_automorphism_nu_target_detects X k s t x u a ha

private def boundarySuspensionNatIso (q : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,-(q:ℤ)) ≅
      SyntheticCategory.biShift (0,-(q:ℤ)) ⋙ shiftFunctor SyntheticSpectrum (1:ℤ) :=
  NatIso.ofComponents (fun A => biSuspensionIso q A)
    (fun f => biSuspensionIso_natural q f)

/-- The boundary comparison is natural even though the exact shift's ordinary
suspension comparison need not be the canonical bigraded commutator. -/
private def boundaryShiftNatIso (e : ℤ) (q : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,-(q:ℤ)) ⋙
        SyntheticCategory.biShift (0,e) ≅
      SyntheticCategory.biShift (0,e) ⋙ SyntheticCategory.biShift (1,-(q:ℤ)) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let J := boundarySuspensionNatIso q
  let C := shiftCommIso (0,e) (0,-(q:ℤ))
  letI := model.exactness.shiftCommShift (0,e)
  exact Functor.isoWhiskerRight J F ≪≫ Functor.associator L S F ≪≫
    Functor.isoWhiskerLeft L (F.commShiftIso (1:ℤ)) ≪≫
    (Functor.associator L F S).symm ≪≫ Functor.isoWhiskerRight C.symm S ≪≫
    Functor.associator F L S ≪≫ Functor.isoWhiskerLeft F J.symm

private theorem boundaryShiftNatIso_app (e : ℤ) (q : ℕ) (A : SyntheticSpectrum) :
    (boundaryShiftNatIso e q).app A =
      (SyntheticCategory.biShift (0,e)).mapIso (biSuspensionIso q A) ≪≫
        (by letI := model.exactness.shiftCommShift (0,e)
            exact ((SyntheticCategory.biShift (0,e)).commShiftIso (1:ℤ)).app _) ≪≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
          ((shiftCommIso (0,e) (0,-(q:ℤ))).symm.app A) ≪≫
        (biSuspensionIso q ((SyntheticCategory.biShift (0,e)).obj A)).symm := by
  apply Iso.ext
  simp only [boundaryShiftNatIso,boundarySuspensionNatIso,Iso.app_hom,
    Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom,Functor.whiskerRight_app,Functor.whiskerLeft_app,
    Functor.associator_hom_app,Functor.associator_inv_app,NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app,Functor.mapIso_hom,Category.id_comp]

/-- A quotient comparison chosen from the canonical lambda square, retaining
the complete boundary square with the natural comparison above. -/
private theorem quotient_boundary_shift_natural_exists
    (A : SyntheticSpectrum) (e : ℤ) (q : ℕ) :
    ∃ eQ : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) q ≅
        (SyntheticCategory.biShift (0,e)).obj (XModLambdaN A q),
      XModLambdaN.incl ((SyntheticCategory.biShift (0,e)).obj A) q ≫ eQ.hom =
        (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl A q) ∧
      eQ.hom ≫ (SyntheticCategory.biShift (0,e)).map (absoluteBoundary A q) ≫
          (boundaryShiftNatIso e q).hom.app A =
        absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj A) q := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  let C := (shiftCommIso (0,e) (0,-(q:ℤ))).app A
  let T := Triangle.mk (lambdaPow q A) (XModLambdaN.incl A q) (XModLambdaN.proj A q)
  let T' := Triangle.mk (lambdaPow q (F.obj A))
    (XModLambdaN.incl (F.obj A) q) (XModLambdaN.proj (F.obj A) q)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  let E := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) C (Iso.refl _) (by
      change lambdaPow q (F.obj A) ≫ 𝟙 _ = C.hom ≫ F.map (lambdaPow q A)
      simpa only [Category.comp_id,C,F,lambdaDegree,Iso.app_hom] using
        lambdaPow_shift_comm (0,e) q A)
  refine ⟨Triangle.π₃.mapIso E,?_,?_⟩
  · have h := E.hom.comm₂
    change XModLambdaN.incl (F.obj A) q ≫ E.hom.hom₃ =
      E.hom.hom₂ ≫ F.map (XModLambdaN.incl A q) at h
    change XModLambdaN.incl (F.obj A) q ≫ E.hom.hom₃ =
      F.map (XModLambdaN.incl A q)
    simpa only [E,isoTriangleOfIso₁₂_hom_hom₂,Iso.refl_hom,Category.id_comp] using h
  · have h := E.hom.comm₃
    have h₁ : E.hom.hom₁ = C.hom := by
      simp only [E,isoTriangleOfIso₁₂_hom_hom₁]
    rw [h₁] at h
    change XModLambdaN.proj (F.obj A) q ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map C.hom =
      E.hom.hom₃ ≫ (F.map (XModLambdaN.proj A q) ≫
        (F.commShiftIso (1:ℤ)).hom.app _) at h
    have hh := congrArg (fun z => z ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map C.inv ≫
      (biSuspensionIso q (F.obj A)).inv) h.symm
    simp only [Category.assoc,Iso.map_hom_inv_id_assoc] at hh
    change E.hom.hom₃ ≫ F.map (absoluteBoundary A q) ≫
      (boundaryShiftNatIso e q).hom.app A = absoluteBoundary (F.obj A) q
    change E.hom.hom₃ ≫ F.map (absoluteBoundary A q) ≫
      ((boundaryShiftNatIso e q).app A).hom = absoluteBoundary (F.obj A) q
    rw [boundaryShiftNatIso_app]
    simpa only [absoluteBoundary,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
      Functor.map_comp,Category.assoc,Iso.map_inv_hom_id_assoc,
      Iso.app_hom,Iso.app_inv,C,F] using hh

private theorem natural_automorphism_nu_detects
    (F : SyntheticSpectrum ⥤ SyntheticSpectrum) (ff : F.FullyFaithful) (η : F ≅ F)
    (X : ClassicalObject) (s t w : ℤ) (hw : w≤t)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) a) :
    Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x)
      (a≫ff.preimage (η.hom.app (model.nu.functor.obj (X.obj model.auxiliary)))) := by
  let u : Smn (Syn:=SyntheticSpectrum) (t-s) w ≅ Smn (t-s) w :=
    ff.preimageIso (η.app _)
  have hn : a≫ff.preimage (η.hom.app _) = u.hom≫a := by
    apply ff.map_injective
    simp only [Functor.map_comp,u,Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage,Iso.app_hom]
    exact η.hom.naturality a
  rw [hn]
  exact sphere_automorphism_nu_detects X s t w hw x u a ha

/-- Changing a natural comparison between fully faithful functors is induced,
on each represented homotopy group, by a sphere automorphism. -/
private theorem natural_iso_comparison_sphere
    (F G : SyntheticSpectrum ⥤ SyntheticSpectrum) (ff : F.FullyFaithful)
    (α β : F ≅ G) (m w : ℤ) (A : SyntheticSpectrum) (a : BiHom m w A) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w,
      F.map a ≫ α.hom.app A = F.map (u.hom≫a) ≫ β.hom.app A := by
  let η : F ≅ F := α ≪≫ β.symm
  let u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w := ff.preimageIso (η.app _)
  have hu : F.map u.hom = η.hom.app _ := ff.map_preimage _
  refine ⟨u,?_⟩
  have hn := congrArg (fun z => z≫β.hom.app A) (η.hom.naturality a)
  simpa only [Functor.map_comp,hu,η,Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,
    Category.assoc,Iso.inv_hom_id_app,Category.comp_id] using hn

private theorem natural_iso_comparison_nu_detects
    (F G : SyntheticSpectrum ⥤ SyntheticSpectrum) (ff : F.FullyFaithful)
    (α β : F ≅ G) (X : ClassicalObject) (s t w : ℤ) (hw : w≤t)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) a) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) (t-s) w ≅ Smn (t-s) w,
      Detects (model.convergence (.nu X)) (s,t,w)
        (nuWeightLabel model X s t w hw x) (u.hom≫a) ∧
      F.map a ≫ α.hom.app (model.nu.functor.obj (X.obj model.auxiliary)) =
        F.map (u.hom≫a) ≫ β.hom.app (model.nu.functor.obj (X.obj model.auxiliary)) := by
  obtain ⟨u,hu⟩ := natural_iso_comparison_sphere F G ff α β (t-s) w _ a
  exact ⟨u,sphere_automorphism_nu_detects X s t w hw x u a ha,hu⟩

/-- Raw lambda multiplication commutes with every bigraded shift on actual
homotopy representatives, with only the forced degree reindexing. -/
private theorem lambda_raw_shift_comm
    (δ p : ℤ×ℤ) (k : ℕ) (A : SyntheticSpectrum) (a : BiHom p.1 p.2 A) :
    shiftHomotopyClass δ (p+(0,-(k:ℤ)))
        (shiftHomotopyClass (0,-(k:ℤ)) p a ≫ lambdaPow k A) =
      homotopyRegrade
        (show ((p+δ)+(0,-(k:ℤ))).1=((p+(0,-(k:ℤ)))+δ).1 by dsimp; omega)
        (show ((p+δ)+(0,-(k:ℤ))).2=((p+(0,-(k:ℤ)))+δ).2 by dsimp; omega)
        (shiftHomotopyClass (0,-(k:ℤ)) (p+δ) (shiftHomotopyClass δ p a) ≫
          lambdaPow k ((SyntheticCategory.biShift δ).obj A)) := by
  rw [shift_hom_comp,regrade_comp,lambdaPow_shift_comm]
  rw [shift_regrade]
  have h := shift_hom_swap p δ (0,-(k:ℤ)) (p+δ) (p+(0,-(k:ℤ)))
    ((p+(0,-(k:ℤ)))+δ) rfl rfl (by ext <;> dsimp <;> omega) rfl a
  have hh := congrArg (fun z => z≫(SyntheticCategory.biShift δ).map (lambdaPow k A)) h.symm
  simpa only [shiftHomotopyClass,biShiftAddIso,eqToIso_refl,Iso.trans_refl,
    Category.assoc,lambdaDegree,Prod.eta] using hh

private theorem sphere_automorphism_nu_frame
    (X : ClassicalObject) (p : ℤ×ℤ) (s : ℤ) (hw : p.2≤p.1+s)
    (x : Ambient model X (s,p.1+s))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _ (nuWeightLabel model X s (p.1+s) p.2 hw x) z)
    (u : Smn (Syn:=SyntheticSpectrum) p.1 p.2 ≅ Smn p.1 p.2)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (model.nu.functor.obj (X.obj model.auxiliary))).F s p) : ModuleCat ℤ))
    (ha : (model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).toAssociatedGraded s p a =
      (infinityGradedIso (model.convergence (.nu X)) p s).hom z) :
    ∃ b : (Subobject.underlying.obj ((model.syntheticTower.filtration
        (model.nu.functor.obj (X.obj model.auxiliary))).F s p) : ModuleCat ℤ),
      ((model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).F s p).arrow b =
        u.hom≫((model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).F s p).arrow a ∧
      (model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).toAssociatedGraded s p b =
        (infinityGradedIso (model.convergence (.nu X)) p s).hom z := by
  have had := source_frame_detects (model.convergence (.nu X)) p s z _ hz a ha
  have H (m : ℤ) (hm : m=(p.1+s)-s)
      (v : Smn (Syn:=SyntheticSpectrum) m p.2 ≅ Smn m p.2)
      (a0 : BiHom m p.2 (model.nu.functor.obj (X.obj model.auxiliary)))
      (h : Detects (model.convergence (.nu X)) (s,p.1+s,p.2)
        (nuWeightLabel model X s (p.1+s) p.2 hw x) (homotopyRegrade hm rfl a0)) :
      Detects (model.convergence (.nu X)) (s,p.1+s,p.2)
        (nuWeightLabel model X s (p.1+s) p.2 hw x) (homotopyRegrade hm rfl (v.hom≫a0)) := by
    subst m
    exact sphere_automorphism_nu_detects X s (p.1+s) p.2 hw x v a0 h
  have hauto := H p.1 (by omega) u _ had
  obtain ⟨z',hz',b,hb,hgb⟩ := frame_of_source_detects (model.convergence (.nu X)) p s
    (nuWeightLabel model X s (p.1+s) p.2 hw x) _ hauto
  rw [hz'.unique hz] at hgb
  exact ⟨b,hb,hgb⟩

private def shiftInfinityClass (A : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).sequence.ssData
      (s,(p+δ).1+s,(p+δ).2)).eInfty :=
  (towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
    ((essShift δ).filtered A p) s).hom z

private theorem infinity_frames_heq
    (A : SyntheticObject) (p q : ℤ×ℤ) (hpq : p=q) (s : ℤ)
    (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (z' : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,q.1+s,q.2)).eInfty)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p) : ModuleCat ℤ))
    (b : (Subobject.underlying.obj ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s q) : ModuleCat ℤ))
    (ha : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s p a =
      (infinityGradedIso (model.convergence A) p s).hom z)
    (hb : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s q b =
      (infinityGradedIso (model.convergence A) q s).hom z')
    (hab : homotopyRegrade (congrArg Prod.fst hpq.symm) (congrArg Prod.snd hpq.symm)
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s q).arrow b) =
      ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a) : HEq z z' := by
  subst q
  have hba : b=a := (ModuleCat.mono_iff_injective
    ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow).mp inferInstance hab
  subst b
  exact heq_of_eq ((infinityGradedIso (model.convergence A) p s).toLinearEquiv.injective
    (ha.symm.trans hb))

/-- Every natural interchange of two shifts induces the same double-shift
comparison on the specified nu infinity labels. -/
private theorem shift_comm_natural_infinity_nu
    (δ ε : ℤ×ℤ)
    (N : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ ⋙ SyntheticCategory.biShift ε ≅
      SyntheticCategory.biShift ε ⋙ SyntheticCategory.biShift δ)
    (X : ClassicalObject) (p : ℤ×ℤ) (s : ℤ) (hw : p.2≤p.1+s)
    (x : Ambient model X (s,p.1+s))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _ (nuWeightLabel model X s (p.1+s) p.2 hw x) z) :
    HEq
      ((model.family.map (N.hom.app (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
        (s,((p+δ)+ε).1+s,((p+δ)+ε).2)
        (shiftInfinityClass (.shift δ (.nu X)) ε (p+δ) s (shiftInfinityClass (.nu X) δ p s z)))
      (shiftInfinityClass (.shift ε (.nu X)) δ (p+ε) s (shiftInfinityClass (.nu X) ε p s z)) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := model.syntheticTower.filtration A
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence (.nu X)) p s).hom z)
  let a := (F.F s p).arrow ar
  obtain ⟨u,hu⟩ := natural_iso_comparison_sphere
    (SyntheticCategory.biShift δ ⋙ SyntheticCategory.biShift ε)
    (SyntheticCategory.biShift ε ⋙ SyntheticCategory.biShift δ)
    ((SyntheticCategory.biShift_fullyFaithful δ).comp (SyntheticCategory.biShift_fullyFaithful ε))
    N (shiftCommIso δ ε) p.1 p.2 A a
  obtain ⟨ar',har',hgar'⟩ := sphere_automorphism_nu_frame X p s hw x z hz u ar har
  obtain ⟨br,hbr,hgbr⟩ := shift_frame (.nu X) δ p s z ar har
  obtain ⟨cr,hcr,hgcr⟩ := shift_frame (.shift δ (.nu X)) ε (p+δ) s _ br hgbr
  obtain ⟨dr,hdr,hgdr⟩ := tower_map_frame
    (model.convergentMap (.shift ε (.shift δ (.nu X))) (.shift δ (.shift ε (.nu X)))
      (N.hom.app A)) ((p+δ)+ε) s _ cr hgcr
  obtain ⟨br',hbr',hgbr'⟩ := shift_frame (.nu X) ε p s z ar' hgar'
  obtain ⟨cr',hcr',hgcr'⟩ := shift_frame (.shift ε (.nu X)) δ (p+ε) s _ br' hgbr'
  have hpq : (p+δ)+ε=(p+ε)+δ := by ext <;> dsimp <;> omega
  apply infinity_frames_heq (.shift δ (.shift ε (.nu X)))
    ((p+δ)+ε) ((p+ε)+δ) hpq s _ _ dr cr' hgdr hgcr'
  rw [←hdr,hcr,hbr,hcr',hbr']
  change homotopyRegrade _ _
    (shiftHomotopyClass δ (p+ε) (shiftHomotopyClass ε p ((F.F s p).arrow ar'))) =
      shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a) ≫ N.hom.app A
  change (F.F s p).arrow ar' = u.hom≫a at har'
  rw [har']
  have hN : shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a) ≫ N.hom.app A =
      shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p (u.hom≫a)) ≫
        (shiftCommIso δ ε).hom.app A := by
    have hh := congrArg (fun v => (SyntheticCategory.biShift_comp (p+δ) ε).inv.app S_0_0 ≫
      (SyntheticCategory.biShift ε).map ((SyntheticCategory.biShift_comp p δ).inv.app S_0_0) ≫ v) hu
    simpa only [shiftHomotopyClass,Functor.map_comp,Functor.comp_map,Category.assoc] using hh
  have hC : shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p (u.hom≫a)) ≫
        (shiftCommIso δ ε).hom.app A =
      homotopyRegrade (congrArg Prod.fst hpq.symm) (congrArg Prod.snd hpq.symm)
        (shiftHomotopyClass δ (p+ε) (shiftHomotopyClass ε p (u.hom≫a))) := by
    rcases δ with ⟨d₁,d₂⟩
    rw [shift_regrade]
    have hh := shift_hom_swap p (d₁,d₂) ε (p+(d₁,d₂)) (p+ε) ((p+(d₁,d₂))+ε)
      rfl rfl rfl hpq.symm (u.hom≫a)
    simpa only [shiftHomotopyClass,biShiftAddIso,eqToIso_refl,Iso.trans_refl,Prod.eta,
      Category.assoc] using hh
  exact (hN.trans hC).symm


set_option backward.defeqAttrib.useBackward false

private theorem infinity_frame_heq_of_arrow_heq
    (A : SyntheticObject) (p q : ℤ×ℤ) (hpq : p=q) (s : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,q.1+s,q.2)).eInfty)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F s p) : ModuleCat ℤ))
    (b : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F s q) : ModuleCat ℤ))
    (ha : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s p a =
      (infinityGradedIso (model.convergence A) p s).hom x)
    (hb : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s q b =
      (infinityGradedIso (model.convergence A) q s).hom y)
    (hab : HEq (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a)
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s q).arrow b)) :
    HEq x y := by
  subst q
  have hab' : a=b := (ModuleCat.mono_iff_injective
    ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow).mp
      inferInstance (eq_of_heq hab)
  subst b
  exact heq_of_eq ((infinityGradedIso (model.convergence A) p s).toLinearEquiv.injective
    (ha.symm.trans hb))

private theorem homotopyRegrade_heq {A : SyntheticSpectrum}
    {m n w v : ℤ} (hm : m=n) (hw : w=v) (a : BiHom m w A) :
    HEq (homotopyRegrade hm hw a) a := by
  subst n
  subst v
  rfl

private theorem lambdaRawInfinity_shift_comm
    (A : SyntheticObject) (δ p : ℤ×ℤ) (k : ℕ) (s : ℤ)
    (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    HEq
      ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
        ((essShift δ).filtered A (p+(0,-(k:ℤ)))) s).hom
          (lambdaRawInfinity A k p s z))
      (lambdaRawInfinity (.shift δ A) k (p+δ) s
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
          ((essShift δ).filtered A p) s).hom z)) := by
  let F := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence A) p s).hom z)
  obtain ⟨br,hbr,hgbr⟩ := shift_frame A (0,-(k:ℤ)) p s z ar har
  obtain ⟨cr,hcr,hgcr⟩ := tower_map_frame
    (model.convergentMap (.shift (0,-(k:ℤ)) A) A (lambdaPow k (A.obj model.nu model.auxiliary)))
    (p+(0,-(k:ℤ))) s _ br hgbr
  obtain ⟨dr,hdr,hgdr⟩ := shift_frame A δ (p+(0,-(k:ℤ))) s _ cr hgcr
  obtain ⟨br',hbr',hgbr'⟩ := shift_frame A δ p s z ar har
  obtain ⟨cr',hcr',hgcr'⟩ := shift_frame (.shift δ A) (0,-(k:ℤ)) (p+δ) s _ br' hgbr'
  obtain ⟨dr',hdr',hgdr'⟩ := tower_map_frame
    (model.convergentMap (.shift (0,-(k:ℤ)) (.shift δ A)) (.shift δ A)
      (lambdaPow k ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)))
    ((p+δ)+(0,-(k:ℤ))) s _ cr' hgcr'
  apply infinity_frame_heq_of_arrow_heq (.shift δ A)
    ((p+(0,-(k:ℤ)))+δ) ((p+δ)+(0,-(k:ℤ))) (by abel) s _ _ dr dr' hgdr hgdr'
  rw [hdr,←hcr,hbr,←hdr',hcr',hbr']
  exact (heq_of_eq (lambda_raw_shift_comm δ p k _ _)).trans
    (homotopyRegrade_heq _ _ _)


private theorem absolute_boundary_class_shift (A : SyntheticSpectrum)
    (q : ℕ) (m w : ℤ) (a : BiHom m w (XModLambdaN A q)) :
    a ≫ absoluteBoundary A q =
      homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w (q:ℤ))
        (shiftHomotopyClass (1,-(q:ℤ)) (m-1,w+q)
          (biSuspensionHomEquiv m w q A (a ≫ XModLambdaN.proj A q))) := by
  let α := biSuspensionHomEquiv m w q A (a ≫ XModLambdaN.proj A q)
  have h := congrArg (fun z => z ≫ (biSuspensionIso q A).inv)
    (bi_susp_symm_eq m w q A α)
  simpa [α,absoluteBoundary,shiftHomotopyClass,susp_invariance,Iso.homCongr] using h

private theorem differential_absolute_boundary_labelled (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k)) :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
      Detects (model.convergence (.quotient i (.nu X))) (s,(t-s)+s,t)
        (regradeE2 (show (s,t,t)=(s,(t-s)+s,t) by simp)
          (regradeE2 (show (s,t,t-(0:ℕ))=(s,t,t) by simp)
            (finiteTargetLabel model X i s t 0 x)))
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (model.convergence (.shift (1,-(i:ℤ)) (.nu X)))
        (s+k+1,(t-s)+(s+k+1),t)
        (regradeE2 (by ext <;> dsimp <;> omega)
          (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
            ((t-s)-1,t+i) (s+k+1)).hom
              (regradeE2 (by ext <;> dsimp <;> omega)
                (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y))))
        (homotopyRegrade (by dsimp; omega) rfl
          (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i)) := by
  obtain ⟨a,ha,hδ⟩ := differential_absolute_boundary X i k hi hik s t x y hd hy
  refine ⟨a,?_,?_⟩
  · have hs := first_label_detects_unshifted X i hi s t x a ha
    have h := detects_transport (show (s,t,t)=(s,(t-s)+s,t) by simp) _ _ hs
    simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using h
  · let α := biSuspensionHomEquiv (t-s) t i
      (model.nu.functor.obj (X.obj model.auxiliary)) (a ≫ XModLambdaN.proj _ i)
    have hs : Detects (model.convergence (.nu X))
        (s+k+1,((t-s)-1)+(s+k+1),t+i)
        (regradeE2 (by ext <;> dsimp <;> omega)
          (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y))
        (homotopyRegrade (by dsimp; omega) rfl α) := by
      have h := detects_transport
        (show (s+k+1,t+k,t+i)=(s+k+1,((t-s)-1)+(s+k+1),t+i) by
          ext <;> dsimp <;> omega) _ _ hδ
      simpa only [α,regrade_precomp,←Category.assoc,eqToHom_trans] using h
    have hb := detects_shift (.nu X) ((1:ℤ),-(i:ℤ)) ((t-s)-1,t+i) (s+k+1) _ α hs
    have hp : (s+k+1,(((t-s)-1,t+i)+((1:ℤ),-(i:ℤ))).1+(s+k+1),
          (((t-s)-1,t+i)+((1:ℤ),-(i:ℤ))).2)=(s+k+1,(t-s)+(s+k+1),t) := by
        ext <;> dsimp <;> omega
    have H := detects_transport hp _ _ hb
    rw [absolute_boundary_class_shift]
    simpa only [α,regrade_precomp,←Category.assoc,eqToHom_trans] using H

private def differentialBoundaryInfinity (X : ClassicalObject)
    (i k : ℕ) (hik : i ≤ k) (s t : ℤ)
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s+k+1,(t-s)+(s+k+1),t)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s+k+1,p.1+(s+k+1),p.2)).eInfty)
      (show lambdaBoundaryPoint (k-i) i ((t-s)-1,t+k)=(t-s,t) by
        ext <;> dsimp [lambdaBoundaryPoint] <;> omega)))
    (lambdaBoundaryInfinity (.nu X) (k-i) i ((t-s)-1,t+k) (s+k+1) z)

set_option maxHeartbeats 200000 in
private theorem differential_boundary_infinity_representative (X : ClassicalObject)
    (i k : ℕ) (hik : i ≤ k) (s t : ℤ)
    (y : Ambient model X (s+k+1,t+k))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp <;> omega)
        (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y)) z) :
    HasInfinityRepresentative _ 2 (s+k+1,(t-s)+(s+k+1),t)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
          ((t-s)-1,t+i) (s+k+1)).hom
            (regradeE2 (by ext <;> dsimp <;> omega)
              (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y))))
      (differentialBoundaryInfinity X i k hik s t z) := by
  let p : ℤ×ℤ := ((t-s)-1,t+k)
  let p' : ℤ×ℤ := ((t-s)-1,t+i)
  have hp : p+((0:ℤ),-((k-i:ℕ):ℤ))=p' := by ext <;> dsimp [p,p'] <;> omega
  let target : (model.family.nu model.nu (X.obj model.auxiliary)).E₂
      (s+k+1,p'.1+(s+k+1),p'.2) :=
    regradeE2 (by ext <;> dsimp [p']; omega)
      (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y)
  let targetRaw : (model.family.nu model.nu (X.obj model.auxiliary)).E₂
      (s+k+1,(p+((0:ℤ),-((k-i:ℕ):ℤ))).1+(s+k+1),
        (p+((0:ℤ),-((k-i:ℕ):ℤ))).2) :=
    regradeE2 (congrArg (fun v : ℤ×ℤ => (s+k+1,v.1+(s+k+1),v.2)) hp.symm) target
  have htargetRaw : HEq targetRaw
      (nuWeightLabel model X (s+k+1) (t+k) (p.2-((k-i:ℕ):ℤ)) (by dsimp [p]; omega) y) := by
    apply (regradeE2_heq _ target).trans
    apply (regradeE2_heq _ _).trans
    exact nuWeight_label_heq X _ _ _ _ _ _ rfl rfl (by dsimp [p]; omega) _ _ _ _ HEq.rfl
  have hraw := lambdaRawInfinity_nu_representative_regraded X (k-i) p (s+k+1) (t+k)
    (by dsimp [p]; omega) (by dsimp [p]; omega) y _ (regradeE2_heq _ _) z hz
    _ (by ext <;> dsimp [p] <;> omega) targetRaw htargetRaw
    (lambdaRawInfinity (.nu X) (k-i) p (s+k+1) z) HEq.rfl
  have hbound := ((essShift (1,-(i:ℤ))).representative_iff (.nu X) 2 (by decide)
    (p+((0:ℤ),-((k-i:ℕ):ℤ))) (s+k+1) targetRaw
    (lambdaRawInfinity (.nu X) (k-i) p (s+k+1) z)).mp hraw
  have hpoint : (s+k+1,(lambdaBoundaryPoint (k-i) i p).1+(s+k+1),
      (lambdaBoundaryPoint (k-i) i p).2)=(s+k+1,(t-s)+(s+k+1),t) := by
    ext <;> dsimp [lambdaBoundaryPoint,p] <;> omega
  have hbound := representative_transport hpoint _ _ hbound
  have hshift (a b : ℤ×ℤ) (hab : a=b)
      (x : (model.family.nu model.nu (X.obj model.auxiliary)).E₂ (s+k+1,a.1+(s+k+1),a.2))
      (y : (model.family.nu model.nu (X.obj model.auxiliary)).E₂ (s+k+1,b.1+(s+k+1),b.2))
      (hxy : HEq x y) :
      HEq (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) a (s+k+1)).hom x)
        (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) b (s+k+1)).hom y) := by
    subst b
    cases hxy
    rfl
  let labelA := ((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
    (p+((0:ℤ),-((k-i:ℕ):ℤ))) (s+k+1)).hom targetRaw
  let labelB := ((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) p' (s+k+1)).hom target
  have hshiftxy := hshift (p+((0:ℤ),-((k-i:ℕ):ℤ))) p' hp targetRaw target
    (regradeE2_heq _ target)
  have hlabel := (regradeE2_heq hpoint labelA).trans hshiftxy
  have hcan : (s+k+1,(p'+((1:ℤ),-(i:ℤ))).1+(s+k+1),
      (p'+((1:ℤ),-(i:ℤ))).2)=(s+k+1,(t-s)+(s+k+1),t) := by
    ext <;> dsimp [p'] <;> omega
  let finalLabel : (model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).E₂ (s+k+1,(t-s)+(s+k+1),t) :=
    regradeE2 hcan labelB
  have hfinal : HEq finalLabel labelB := regradeE2_heq hcan labelB
  have hlabel' := hlabel.trans hfinal.symm
  have hlabelEq := eq_of_heq hlabel'
  rw [hlabelEq] at hbound
  exact hbound

private theorem differential_absolute_boundary_extension (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k))
    (zF : ((model.family.obj ((SyntheticObject.quotient i (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,(t-s)+s,t)).eInfty)
    (hzF : HasInfinityRepresentative _ 2 _
      (regradeE2 (show (s,t,t)=(s,(t-s)+s,t) by simp)
        (regradeE2 (show (s,t,t-(0:ℕ))=(s,t,t) by simp)
          (finiteTargetLabel model X i s t 0 x))) zF)
    (zI : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty)
    (hzI : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp <;> omega)
        (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y)) zI) :
    TowerExtensionEquation
      (model.convergentMap (.quotient i (.nu X)) (.shift (1,-(i:ℤ)) (.nu X))
        (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i))
      (t-s,t) s (k+1) zF
      ((eqToHom (congrArg (fun p =>
        ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
          model.nu model.auxiliary)).sequence.ssData p).eInfty)
          (show (s+k+1,(t-s)+(s+k+1),t)=(s+(k+1),(t-s)+(s+(k+1)),t) by
            ext <;> dsimp <;> omega)))
        (differentialBoundaryInfinity X i k hik s t zI)) := by
  obtain ⟨a,ha,hδ⟩ := differential_absolute_boundary_labelled X i k hi hik s t x y hd hy
  have hp : (s+k+1,(t-s)+(s+k+1),t)=(s+(k+1),(t-s)+(s+(k+1)),t) := by
    ext <;> dsimp <;> omega
  have hδ' := detects_transport hp _ _ hδ
  have htarget := representative_transport hp _ _
    (differential_boundary_infinity_representative X i k hik s t y zI hzI)
  obtain ⟨z₀,z₁,hz₀,hz₁,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.quotient i (.nu X)) (.shift (1,-(i:ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i))
      (t-s,t) s (k+1) (by omega) _ _ a
      (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i) ha
      (by simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using hδ') rfl
  rw [hz₀.unique hzF,hz₁.unique htarget] at heq
  exact heq

private theorem left_infinity_shift_heq (A : SyntheticObject) (δ : ℤ×ℤ)
    (p p' : ℤ×ℤ) (s s' : ℤ) (hp : p=p') (hs : s=s')
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s',p'.1+s',p'.2)).eInfty) (hxy : HEq x y) :
    HEq ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
      ((essShift δ).filtered A p) s).hom x)
      ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
        ((essShift δ).filtered A p') s').hom y) := by
  subst p'
  subst s'
  cases hxy
  rfl

private theorem left_infinity_map_heq {A B : SyntheticSpectrum} (g : A ⟶ B)
    (i j : Tridegree) (hij : i=j)
    (x : ((model.family.obj A).sequence.ssData i).eInfty)
    (y : ((model.family.obj A).sequence.ssData j).eInfty) (hxy : HEq x y) :
    HEq ((model.family.map g).eInftyMap i x)
      ((model.family.map g).eInftyMap j y) := by
  subst j
  cases hxy
  rfl

private theorem left_lambdaBoundaryInfinity_heq (A : SyntheticObject)
    (k k' q q' : ℕ) (p p' : ℤ×ℤ) (s s' : ℤ)
    (hk : k=k') (hq : q=q') (hp : p=p') (hs : s=s')
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s',p'.1+s',p'.2)).eInfty) (hxy : HEq x y) :
    HEq (lambdaBoundaryInfinity A k q p s x) (lambdaBoundaryInfinity A k' q' p' s' y) := by
  subst k'; subst q'; subst p'; subst s'
  cases hxy
  rfl

private theorem lambdaBoundaryInfinity_vertical_comm_nu
    (X : ClassicalObject) (e : ℤ) (k q : ℕ) (p : ℤ×ℤ) (s : ℤ)
    (hw : p.2 ≤ p.1+s) (x : Ambient model X (s,p.1+s))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _
      (nuWeightLabel model X s (p.1+s) p.2 hw x) z) :
    HEq
      ((model.family.map ((boundaryShiftNatIso e q).hom.app
        (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
          (s,((lambdaBoundaryPoint k q p)+((0:ℤ),e)).1+s,
            ((lambdaBoundaryPoint k q p)+((0:ℤ),e)).2)
          (shiftInfinityClass (.shift (1,-(q:ℤ)) (.nu X)) ((0:ℤ),e)
            (lambdaBoundaryPoint k q p) s (lambdaBoundaryInfinity (.nu X) k q p s z)))
      (lambdaBoundaryInfinity (.shift ((0:ℤ),e) (.nu X)) k q (p+((0:ℤ),e)) s
        (shiftInfinityClass (.nu X) ((0:ℤ),e) p s z)) := by
  let K : ℤ×ℤ := (0,-(k:ℤ))
  let E : ℤ×ℤ := (0,e)
  let D : ℤ×ℤ := (1,-(q:ℤ))
  let pK := p+K
  let xK : Ambient model X (s,pK.1+s) :=
    (eqToHom (congrArg (fun i => Ambient model X i)
      (show (s,p.1+s)=(s,pK.1+s) by simp [pK,K]))) x
  let ξ := lambdaRawInfinity (.nu X) k p s z
  have hxK : HEq xK x := eqToHom_apply_heq _ x
  have hξ : HasInfinityRepresentative _ 2 (s,pK.1+s,pK.2)
      (nuWeightLabel model X s (pK.1+s) pK.2 (by dsimp [pK,K]; omega) xK) ξ := by
    apply lambdaRawInfinity_nu_representative X k p s hw x z hz
      (s,pK.1+s,pK.2) (by ext <;> dsimp [pK,K] <;> omega)
      _ _ ξ HEq.rfl
    exact nuWeight_label_heq X _ _ _ _ _ _ rfl
      (by simp [pK,K]) (by simp [pK,K]; omega) _ _ _ _ hxK
  have hδ := shift_comm_natural_infinity_nu D E (boundaryShiftNatIso e q)
    X pK s (by dsimp [pK,K]; omega) xK ξ hξ
  have hLambda := lambdaRawInfinity_shift_comm (.nu X) E p k s z
  have hdeltaLambda := left_infinity_shift_heq (.shift E (.nu X)) D
    (pK+E) ((p+E)+K) s s (by dsimp [pK]; abel) rfl _ _ hLambda
  exact hδ.trans hdeltaLambda

private def normalizedDifferentialBoundaryInfinity (X : ClassicalObject)
    (e : ℤ) (i k : ℕ) (hik : i ≤ k) (s t : ℤ)
    (z : ((model.family.obj ((SyntheticObject.shift ((0:ℤ),e) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData
        (s+k+1,(((t+k)-(s+k+1),t+k)+((0:ℤ),e)).1+(s+k+1),
          (((t+k)-(s+k+1),t+k)+((0:ℤ),e)).2)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ))
      (.shift ((0:ℤ),e) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
        (s+(k+1),((t-s,t)+((0:ℤ),e)).1+(s+(k+1)),
          ((t-s,t)+((0:ℤ),e)).2)).eInfty :=
  (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ))
      (.shift ((0:ℤ),e) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData j).eInfty)
      (show (s+k+1,
          (lambdaBoundaryPoint (k-i) i (((t+k)-(s+k+1),t+k)+((0:ℤ),e))).1+(s+k+1),
          (lambdaBoundaryPoint (k-i) i (((t+k)-(s+k+1),t+k)+((0:ℤ),e))).2)=
          (s+(k+1),((t-s,t)+((0:ℤ),e)).1+(s+(k+1)),((t-s,t)+((0:ℤ),e)).2) by
        ext <;> dsimp [lambdaBoundaryPoint] <;> omega)))
    (lambdaBoundaryInfinity (.shift ((0:ℤ),e) (.nu X)) (k-i) i
      (((t+k)-(s+k+1),t+k)+((0:ℤ),e)) (s+k+1) z)

set_option maxHeartbeats 200000 in
private theorem differential_absolute_boundary_normalized_extension
    (X : ClassicalObject) (e : ℤ) (he : e=0 ∨ e=1)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k))
    (zFN : ((model.family.obj ((SyntheticObject.quotient i (.shift ((0:ℤ),e) (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData
        (s,((t-s,t)+((0:ℤ),e)).1+s,((t-s,t)+((0:ℤ),e)).2)).eInfty)
    (hzFN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> simp) (finiteNuLabel model X i e s t 0 x)) zFN)
    (zIN : ((model.family.obj ((SyntheticObject.shift ((0:ℤ),e) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData
        (s+k+1,(((t+k)-(s+k+1),t+k)+((0:ℤ),e)).1+(s+k+1),
          (((t+k)-(s+k+1),t+k)+((0:ℤ),e)).2)).eInfty)
    (hzIN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> simp) (model.comparison.nuE2 X e (s+k+1) (t+k) 0 y)) zIN) :
    TowerExtensionEquation
      (model.convergentMap (.quotient i (.shift ((0:ℤ),e) (.nu X)))
        (.shift (1,-(i:ℤ)) (.shift ((0:ℤ),e) (.nu X)))
        (absoluteBoundary ((SyntheticCategory.biShift ((0:ℤ),e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) i))
      ((t-s,t)+((0:ℤ),e)) s (k+1) zFN
      (normalizedDifferentialBoundaryInfinity X e i k hik s t zIN) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let E : ℤ×ℤ := (0,e)
  let D : ℤ×ℤ := (1,-(i:ℤ))
  let p : ℤ×ℤ := (t-s,t)
  let pI : ℤ×ℤ := ((t+k)-(s+k+1),t+k)
  obtain ⟨a,ha,_⟩ := differential_absolute_boundary X i k hi hik s t x y hd hy
  obtain ⟨zF,hzF,_⟩ := first_label_detects_unshifted X i hi s t x a ha
  have hpF : (s,t,t)=(s,p.1+s,p.2) := by simp [p]
  let zFs := (eqToHom (congrArg (fun j =>
    ((model.family.obj (XModLambdaN A i)).sequence.ssData j).eInfty) hpF)) zF
  have hzFs := representative_transport hpF _ _ hzF
  let zI := (KIP126.Literature.Standard.infinityNuWindow X (s+k+1,t+k) (t+k) (by omega)).symm
    (subquotientClass (permanentCycles model X (s+k+1,t+k))
      (boundaries model X (1+(t+k)-(t+k)) (s+k+1,t+k)) ⟨y,hy⟩)
  have hzI : HasInfinityRepresentative _ 2 (s+k+1,t+k,t+k)
      (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y) zI := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X (s+k+1) (t+k) (t+k)
      (by omega) y zI).mpr
    exact ⟨hy,(KIP126.Literature.Standard.infinityNuWindow X (s+k+1,t+k) (t+k)
      (by omega)).apply_symm_apply _⟩
  have hpI : (s+k+1,t+k,t+k)=(s+k+1,pI.1+(s+k+1),pI.2) := by simp [pI]
  let zIs := (eqToHom (congrArg (fun j =>
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData j).eInfty) hpI)) zI
  have hzIs := representative_transport hpI _ _ hzI
  have hpI' : (s+k+1,t+k,t+k)=(s+k+1,((t-s)-1)+(s+k+1),t+k) := by
    ext <;> dsimp <;> omega
  let zIs' := (eqToHom (congrArg (fun j =>
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData j).eInfty) hpI')) zI
  have hzIs' := representative_transport hpI' _ _ hzI
  have hpB : (s+k+1,(t-s)+(s+k+1),t)=(s+(k+1),p.1+(s+(k+1)),p.2) := by
    ext <;> dsimp [p] <;> omega
  let zB := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift D (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData j).eInfty) hpB))
        (differentialBoundaryInfinity X i k hik s t zIs')
  have hbase := differential_absolute_boundary_extension X i k hi hik s t x y hd hy
    zFs hzFs zIs' hzIs'
  have hshift := ((essShift E).towerExtensionEquation_iff
    (.quotient i (.nu X)) (.shift D (.nu X)) (absoluteBoundary A i)
    p s (k+1) _ _).mp hbase
  obtain ⟨Q,hQ,hδ⟩ := quotient_boundary_shift_natural_exists A e i
  let N := (boundaryShiftNatIso e i).hom.app A
  have hsquare : (SyntheticCategory.biShift E).map (absoluteBoundary A i) ≫ N =
      Q.inv ≫ absoluteBoundary ((SyntheticCategory.biShift E).obj A) i := by
    rw [←hδ]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rfl
  have hmap := tower_extension_map
    (model.convergentMap (.shift E (.quotient i (.nu X))) (.shift E (.shift D (.nu X)))
      ((SyntheticCategory.biShift E).map (absoluteBoundary A i)))
    (model.convergentMap (.quotient i (.shift E (.nu X))) (.shift D (.shift E (.nu X)))
      (absoluteBoundary ((SyntheticCategory.biShift E).obj A) i))
    (model.convergentMap (.shift E (.quotient i (.nu X))) (.quotient i (.shift E (.nu X))) Q.inv)
    (model.convergentMap (.shift E (.shift D (.nu X))) (.shift D (.shift E (.nu X))) N)
    hsquare (p+E) s (k+1) _ _ hshift
  have hsource := normalized_finite_source_infinity_shift X i hi e s t he Q hQ x zF hzF zFN hzFN
  have hsourceI := normalized_source_infinity_shift X e (s+k+1) (t+k) he y zI hzI zIN hzIN
  have hpointI : (s+k+1,t+k)=(s+k+1,pI.1+(s+k+1)) := by simp [pI]
  let yI : Ambient model X (s+k+1,pI.1+(s+k+1)) :=
    (eqToHom (congrArg (fun j => Ambient model X j) hpointI)) y
  have hyy : HEq y yI := (eqToHom_apply_heq _ y).symm
  have hwI : pI.2 ≤ pI.1+(s+k+1) := by dsimp [pI]; omega
  let labelI := nuWeightLabel model X (s+k+1) (pI.1+(s+k+1)) pI.2 hwI yI
  have hlabelI : HEq (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y) labelI :=
    nuWeight_label_heq X _ _ _ _ _ _ rfl (by simp [pI]) rfl _ _ _ _ hyy
  have hzRaw : HasInfinityRepresentative (model.family.nu model.nu (X.obj model.auxiliary))
      2 (s+k+1,pI.1+(s+k+1),pI.2) labelI zIs := by
    exact representative_heq_transport _ _ _ rfl _ _ _ _
      ((regradeE2_heq hpI _).trans hlabelI) HEq.rfl hzIs
  have hraw := lambdaBoundaryInfinity_vertical_comm_nu X e (k-i) i pI (s+k+1)
    hwI yI zIs hzRaw
  have hbaseTarget : HEq zB (lambdaBoundaryInfinity (.nu X) (k-i) i pI (s+k+1) zIs) := by
    apply (eqToHom_apply_heq _ _).trans
    apply (eqToHom_apply_heq _ _).trans
    apply left_lambdaBoundaryInfinity_heq (.nu X) (k-i) (k-i) i i
      ((t-s)-1,t+k) pI (s+k+1) (s+k+1) rfl rfl (by ext <;> dsimp [pI] <;> omega) rfl
    exact (eqToHom_apply_heq _ zI).trans (eqToHom_apply_heq _ zI).symm
  have htargetShift := left_infinity_shift_heq (.shift D (.nu X)) E p
    (lambdaBoundaryPoint (k-i) i pI) (s+(k+1)) (s+k+1)
    (by ext <;> dsimp [p,pI,lambdaBoundaryPoint] <;> omega) (by omega)
    _ _ hbaseTarget
  have htargetMap := left_infinity_map_heq N _ _
    (by ext <;> dsimp [p,pI,E,lambdaBoundaryPoint] <;> omega) _ _ htargetShift
  have htargetRaw := htargetMap.trans hraw
  have htargetNorm := left_lambdaBoundaryInfinity_heq (.shift E (.nu X))
    (k-i) (k-i) i i (pI+E) (pI+E) (s+k+1) (s+k+1)
    rfl rfl rfl rfl _ _ (heq_of_eq hsourceI)
  have hcast : HEq (normalizedDifferentialBoundaryInfinity X e i k hik s t zIN)
      (lambdaBoundaryInfinity (.shift E (.nu X)) (k-i) i (pI+E) (s+k+1) zIN) :=
    eqToHom_apply_heq _ _
  have htarget := (htargetRaw.trans htargetNorm).trans hcast.symm
  exact (congrArg₂ (fun a b => TowerExtensionEquation
    (model.convergentMap (.quotient i (.shift E (.nu X))) (.shift D (.shift E (.nu X)))
      (absoluteBoundary ((SyntheticCategory.biShift E).obj A) i))
    (p+E) s (k+1) a b) hsource (eq_of_heq htarget)).mp hmap

private theorem left_nuE2_heq (X : ClassicalObject) (e s t s' t' : ℤ)
    (hs : s=s') (ht : t=t') (x : Ambient model X (s,t)) (y : Ambient model X (s',t'))
    (hxy : HEq x y) :
    HEq (model.comparison.nuE2 X e s t 0 x) (model.comparison.nuE2 X e s' t' 0 y) := by
  subst s'; subst t'
  cases hxy
  rfl

private theorem left_extension_heq (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (p p' : ℤ×ℤ) (hp : p=p') (s n : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (x' : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p'.1+s,p'.2)).eInfty)
    (y : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (y' : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData (s+n,p'.1+(s+n),p'.2)).eInfty)
    (hxx : HEq x x') (hyy : HEq y y')
    (h : TowerExtensionEquation (model.convergentMap A B g) p s n x y) :
    TowerExtensionEquation (model.convergentMap A B g) p' s n x' y' := by
  subst p'
  cases hxx
  cases hyy
  exact h

set_option maxHeartbeats 200000 in
/-- The actual left edge of the GL square for the two specified extension
witnesses. No crossing assumption is needed for this edge. -/
private theorem gl_left_edge (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (r m l s t : ℤ) (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    {x : Ambient model X (s,t)} {y : Ambient model Y (s+m,t+m)}
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      r (s,t) (s+r,t+r-1) x xInfinity)
    (hxInfinity : xInfinity ∈ permanentCycles model X (s+r,t+r-1))
    (WFinite : FiniteExtensionWitness model X Y f page m s t x y)
    (WInfinity : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    TowerExtensionEquation
      (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
        (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (absoluteBoundary ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s r WFinite.source
      (glBottomSource X Y f page r l s t hpage hpr WInfinity) := by
  obtain ⟨k,hkr⟩ : ∃ k : ℕ, r=(k:ℤ)+1 := by
    refine ⟨(r-1).toNat,?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  subst r
  let e : ℤ := normalizedExponent model.classicalTower f
  let E : ℤ×ℤ := (0,e)
  let p : ℤ×ℤ := (t-s,t)
  let pI : ℤ×ℤ := ((t+k)-(s+k+1),t+k)
  have he : e=0 ∨ e=1 := by
    have h := normalizedExponent_le_one model.classicalTower f
    dsimp [e]
    omega
  have hi : 0 < page-1 := by omega
  have hik : page-1 ≤ k := by omega
  have hindex : (s+((k:ℤ)+1),t+((k:ℤ)+1)-1)=(s+k+1,t+k) := by
    ext <;> omega
  let xI : Ambient model X (s+k+1,t+k) :=
    (eqToHom (congrArg (fun v => Ambient model X v) hindex)) xInfinity
  have transport {a b : Bidegree} (hab : a=b) (z : Ambient model X a)
      (hz : z ∈ permanentCycles model X a)
      (hdz : HasDifferential (model.classical.obj (X.obj model.auxiliary)) (k+1) (s,t) a x z) :
      ((eqToHom (congrArg (fun v => Ambient model X v) hab)) z) ∈ permanentCycles model X b ∧
      HasDifferential (model.classical.obj (X.obj model.auxiliary)) (k+1) (s,t) b x
        ((eqToHom (congrArg (fun v => Ambient model X v) hab)) z) := by
    subst b
    exact ⟨hz,hdz⟩
  obtain ⟨hxI,hdI⟩ := transport hindex xInfinity hxInfinity hd
  have hF : (s,(t-s)+s,t+e)=(s,(p+E).1+s,(p+E).2) := by
    ext <;> dsimp [p,E] <;> omega
  let zFN := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.quotient (page-1) (.shift E (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData j).eInfty) hF)) WFinite.source
  have hzFN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp [p,E] <;> omega)
        (finiteNuLabel model X (page-1) e s t 0 x)) zFN := by
    have h := representative_transport hF _ _ WFinite.source_rep
    simpa only [finiteSourceForExtension,extensionSourceObject,e,E,zFN,normalized_regrade_trans] using h
  have hI : (s+((k:ℤ)+1),((t+((k:ℤ)+1)-1)-(s+((k:ℤ)+1)))+(s+((k:ℤ)+1)),
      t+((k:ℤ)+1)-1+e)=(s+k+1,(pI+E).1+(s+k+1),(pI+E).2) := by
    ext <;> dsimp [pI,E] <;> omega
  let zIN := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift E (.nu X)).obj model.nu model.auxiliary)).sequence.ssData j).eInfty)
      hI)) WInfinity.source
  have hzIN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp [pI,E] <;> omega)
        (model.comparison.nuE2 X e (s+k+1) (t+k) 0 xI)) zIN := by
    have h := representative_transport hI _ _ WInfinity.source_rep
    dsimp only [infiniteSourceForExtension] at h
    apply representative_heq_transport _ _ _ rfl _ _ _ _ _ HEq.rfl h
    apply (regradeE2_heq _ _).trans
    apply (regradeE2_heq _ _).trans
    apply HEq.trans _ (regradeE2_heq _ _).symm
    exact left_nuE2_heq X e _ _ _ _ (by omega) (by omega) xInfinity xI
      (eqToHom_apply_heq _ xInfinity).symm
  have hgen := differential_absolute_boundary_normalized_extension X e he
    (page-1) k hi hik s t x xI hdI hxI zFN hzFN zIN hzIN
  have htarget : HEq (normalizedDifferentialBoundaryInfinity X e (page-1) k hik s t zIN)
      (glBottomSource X Y f page ((k:ℤ)+1) l s t hpage hpr WInfinity) := by
    apply (eqToHom_apply_heq _ _).trans
    apply HEq.trans _ (eqToHom_apply_heq _ _).symm
    apply left_lambdaBoundaryInfinity_heq (.shift E (.nu X))
      (k-(page-1)) (((k:ℤ)+1-page).toNat) (page-1) (page-1)
      (pI+E) (((t+((k:ℤ)+1)-1)-(s+((k:ℤ)+1))),t+((k:ℤ)+1)-1+e)
      (s+k+1) (s+((k:ℤ)+1))
      (by omega) rfl (by ext <;> dsimp [pI,E] <;> omega) (by omega)
    exact eqToHom_apply_heq _ WInfinity.source
  exact left_extension_heq (.quotient (page-1) (.shift E (.nu X)))
    (.shift (1,-((page-1:ℕ):ℤ)) (.shift E (.nu X)))
    (absoluteBoundary ((SyntheticObject.shift E (.nu X)).obj model.nu model.auxiliary) (page-1))
    (p+E) (t-s,t+e) (by ext <;> dsimp [p,E] <;> omega) s (k+1)
    zFN WFinite.source _ _ (eqToHom_apply_heq _ WFinite.source) htarget hgen

end
end KIP126.ProofTools.Internal.Leibniz
