module
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
/-!
The positive second-exponent branch of the finite May construction.
The actual normalized connecting map is calibrated against ordinary h₂,
then the same finite representative is inserted into any coefficient layer.
All degree transports retain the prescribed classical source and signed target.
-/
@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem raw_connecting_zero_one_zero {A C D : SyntheticSpectrum}
    (ef eg eh : ℕ) (he : (ef:ℤ)+eg+eh=1)
    (hf : ef=0) (hg : eg=1) (hh : eh=0)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A)
    (g : C ⟶ D) (hfg : lambdaToPositivePow eh C ≫ h=g) :
    raw_normalized_connecting ef eg eh he h σ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (zero_positive_iso A ef hf).hom ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app A =
      (eqToIso (congrArg (fun k : ℕ =>
        (SyntheticCategory.biShift (0,-(k:ℤ))).obj C) hg)).hom ≫
        (SyntheticCategory.biShift (0,-1)).map (g≫σ.hom) ≫
        (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).hom.app A := by
  subst ef; subst eg; subst eh
  have hn := negative_lift_zero_map_form 0 rfl h g hfg
  dsimp only [raw_normalized_connecting,zero_positive_iso,zero_negative_iso] at hn ⊢
  simp only [eqToHom_refl,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,
    Category.id_comp] at hn ⊢
  have hl := model.quotients.coherence.left_unit (1,0) A
  have hr := model.quotients.coherence.right_unit (1,1) A
  dsimp only [biShiftAddIso] at hl hr
  simp only [eqToIso_refl,Iso.trans_refl] at hl hr
  have hκ := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    (SyntheticCategory.biShift_zero.hom.app A)
  dsimp only [Functor.id_obj,Functor.comp_obj,Functor.comp_map] at hκ
  simp only [Iso.app_hom] at hn ⊢
  simp only [Category.assoc]
  erw [←Category.assoc ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _),
    ←hκ,Category.assoc,Iso.hom_inv_id_app,Category.comp_id]
  erw [←hl,Iso.inv_hom_id_app,Category.comp_id]
  erw [hr]
  rw [←Functor.map_comp_assoc,←Functor.map_comp_assoc]
  rw [Category.assoc (negativeLift 0 h)]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  rw [←Category.assoc,hn]
  simp [biShiftAddIso]

private def zeroHShiftedRaw (T : TriangleData model.auxiliary) :
    (SyntheticCategory.biShift (0,-1)).obj (model.nu.functor.obj (T.Z.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (1,0)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  (SyntheticCategory.biShift (0,-1)).map
      (model.nu.functor.map T.h ≫ (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom) ≫
    (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).hom.app _

private theorem normalized_third_arrow_positive_g
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0) :
    (normalizedTriangle model T he).mor₃ ≫ (normalizedSuspensionZeroIso T he hf).hom =
      (normalizedThirdNegativeIso T he hg).hom ≫ zeroHShiftedRaw T := by
  have h := raw_connecting_zero_one_zero _ _ _ he hf hg hh
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (model.nu.suspensionIso (T.X.obj model.auxiliary))
    (model.nu.functor.map T.h)
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).factorization
  simpa only [normalizedTriangle,Triangle.mk,normalizedConnecting,raw_normalized_connecting,
    normalizedSuspensionZeroIso,normalizedThirdNegativeIso,zeroHShiftedRaw,Iso.trans_hom,
    Functor.mapIso_hom,Iso.symm_hom,Iso.app_hom,Category.assoc] using h

private theorem shifted_zero_h_quotient_maps
    (T : TriangleData model.auxiliary)
    (ε₀ : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hε₀ : XModLambdaN.incl _ 1≫ε₀.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1))
    (hε₁ : XModLambdaN.incl _ 1≫ε₁.hom=
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary))) 1)) :
    a≫XModLambdaN.map (zeroHShiftedRaw T) 1≫ε₀.hom =
      a≫(levelQuotientShiftIso T.Z (-1) 1).hom≫
        (SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map (model.nu.functor.map T.h) 1≫
            XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom 1≫ε₁.hom)≫
        (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).hom.app _ := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let E := (model.quotients.functoriality.functor 1).mapIso
    (model.nu.suspensionIso (T.X.obj model.auxiliary)) ≪≫ ε₁
  let D := F.mapIso E ≪≫
    (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).app
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1)
  let f := XModLambdaN.map (zeroHShiftedRaw T) 1≫ε₀.hom
  let g := (levelQuotientShiftIso T.Z (-1) 1).hom≫
    F.map (XModLambdaN.map (model.nu.functor.map T.h) 1)≫D.hom
  have hf : XModLambdaN.incl _ 1≫f = zeroHShiftedRaw T≫
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1) := by
    dsimp only [f]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hε₀]
  have hg : XModLambdaN.incl _ 1≫g = zeroHShiftedRaw T≫
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1) := by
    dsimp only [g]
    rw [←Category.assoc,level_quotient_shift_incl]
    simp only [D,E,Iso.trans_hom,Functor.mapIso_hom,LambdaQuotientFunctoriality.functor,
      Functor.map_comp,Category.assoc]
    rw [←Category.assoc,←F.map_comp,←XModLambdaN.incl_naturality]
    simp only [Functor.map_comp,Category.assoc]
    rw [←Category.assoc (F.map (XModLambdaN.incl _ 1)),←F.map_comp,
      ←XModLambdaN.incl_naturality]
    simp only [Functor.map_comp,Category.assoc]
    rw [←Category.assoc (F.map (XModLambdaN.incl _ 1)),←F.map_comp,hε₁]
    erw [(biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).hom.naturality]
    simp only [zeroHShiftedRaw,F,Functor.map_comp,Category.assoc]
  have hfg : XModLambdaN.incl _ 1≫(f≫D.inv)=XModLambdaN.incl _ 1≫(g≫D.inv) := by
    simpa only [Category.assoc] using congrArg (fun z => z≫D.inv) (hf.trans hg.symm)
  have H := shifted_quotient_sphere_congruence T.Z (.shift 1 T.X) (0,-1) 1 1
    (by decide) le_rfl (levelQuotientShiftIso T.Z (-1) 1)
    (level_quotient_shift_incl T.Z (-1) 1) (f≫D.inv) (g≫D.inv) hfg m w a
  have H' := congrArg (fun z => z≫D.hom) H
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at H'
  simpa only [f,g,D,E,Iso.trans_hom,Functor.mapIso_hom,LambdaQuotientFunctoriality.functor,
    Functor.map_comp,Category.assoc,Iso.app_hom,F] using H'

private theorem shift_hom_compose_canonical (p δ ε θ : ℤ×ℤ) (hθ : δ+ε=θ)
    {A : SyntheticSpectrum} (a : BiHom p.1 p.2 A) :
    homotopyRegrade (by have h := congrArg Prod.fst hθ; dsimp at h ⊢; omega)
        (by have h := congrArg Prod.snd hθ; dsimp at h ⊢; omega)
        (shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a)) ≫
      (biShiftAddIso δ ε θ hθ).hom.app A = shiftHomotopyClass θ p a := by
  have H := shift_hom_associativity model.quotients.coherence
    p δ ε (p+δ) θ (p+θ) rfl hθ (by rw [add_assoc,hθ]) rfl a
  have H' := congrArg (fun z => z≫(biShiftAddIso δ ε θ hθ).hom.app A) H
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at H'
  change homotopyRegrade _ _ (shiftHomotopyClass (ε.1,ε.2)
    ((p+δ).1,(p+δ).2) (shiftHomotopyClass δ p a))≫_ = _
  rw [shift_regrade]
  simpa only [shiftHomotopyClass,biShiftAddIso,eqToIso_refl,Iso.trans_refl,
    Category.assoc] using H'.symm

private theorem zero_h_shifted_first_unshift
    (T : TriangleData model.auxiliary) (s t : ℤ)
    (z : Ambient model T.Z (s,t+1)) (u : Ambient model T.X (s,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((model.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using u))
    (ε₀ : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hε₀ : XModLambdaN.incl _ 1≫ε₀.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1)) :
    quotientUnshift T.X (1,0) (t-s,t) 1 ε₀
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        ((homotopyRegrade (m':=t+1-s) (w':=t) (by simp) (by dsimp;omega)
          (shiftHomotopyClass (0,-1) (t+1-s,t+1) (nativeFirstLabel T.Z s (t+1) z))) ≫
          (levelQuotientShiftIso T.Z (-1) 1).inv ≫ XModLambdaN.map (zeroHShiftedRaw T) 1)) =
      nativeFirstLabel T.X s t u := by
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) 1
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hs := firstQuotient_suspension T.X s t u
    ((model.classical.map T.h).pageMap 2 (s,t+1) z) ε₁ hε₁ hu
  have hl : nativeFirstLabel T.Z s (t+1) z≫XModLambdaN.map (model.nu.functor.map T.h) 1≫
      XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom 1≫ε₁.hom =
      homotopyRegrade (by dsimp;omega) rfl
        (shiftHomotopyClass (1,1) (t-s,t) (nativeFirstLabel T.X s t u)) := by
    rw [←Category.assoc (nativeFirstLabel T.Z s (t+1) z),native_first_label_natural]
    simpa only [nativeFirstLabel_eq_regrade] using hs
  let a : BiHom (t+1-s) t (XModLambdaN ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary))) 1) :=
    homotopyRegrade (by simp) (by dsimp;omega)
      (shiftHomotopyClass (0,-1) (t+1-s,t+1) (nativeFirstLabel T.Z s (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv
  have H := shifted_zero_h_quotient_maps T ε₀ ε₁ hε₀ hε₁ (t+1-s) t a
  simp only [a,Category.assoc,Iso.inv_hom_id_assoc] at H
  have HC := shift_hom_compose_canonical (t-s,t) (1,1) (0,-1) (1,0) (by decide)
    (nativeFirstLabel T.X s t u)
  have HC' := congrArg (homotopyRegrade (m':=t+1-s) (w':=t)
    (by dsimp;omega) (by dsimp;omega)) HC
  simp only [regrade_comp,regrade_transitive] at HC'
  have H' : a≫XModLambdaN.map (zeroHShiftedRaw T) 1≫ε₀.hom =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (1,0) (t-s,t) (nativeFirstLabel T.X s t u)) := by
    dsimp only [a]
    simp only [Category.assoc]
    apply H.trans
    rw [←Category.assoc,←regrade_comp,←shift_hom_comp,hl,
      shift_class_input_regrade,regrade_transitive]
    exact HC'
  apply shift_class_injective (.quotient 1 (.nu T.X)) (1,0) (t-s,t)
  apply (cancel_mono ε₀.inv).mp
  rw [shift_quotient_unshift]
  apply (cancel_mono ε₀.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have Hr := congrArg (homotopyRegrade (m':=((t-s,t)+(1,0)).1)
    (w':=((t-s,t)+(1,0)).2) (by dsimp;omega) (by dsimp;omega)) H'
  have regrade_self {A : SyntheticSpectrum} {m w : ℤ}
      (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a=a := rfl
  simpa only [a,regrade_comp,regrade_transitive,Category.assoc,regrade_self] using Hr

private theorem positive_g_first_desuspend
    (T : TriangleData model.auxiliary) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u))
    (ε₀ : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hε₀ : XModLambdaN.incl _ 1≫ε₀.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
      (quotientShiftDesuspend T.X (1,0) 1 ε₀ (t-s) t
        (homotopyRegrade (by dsimp;omega) (by dsimp;omega)
          (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
            (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
          (levelQuotientShiftIso T.Z (-1) 1).inv ≫ XModLambdaN.map (zeroHShiftedRaw T) 1)) =
      nativeFirstLabel T.X (s+1) t u := by
  erw [quotient_shift_desuspend_as_native_unshift T.X (1,0) (t-(s+1),t) 1 (t-s) t
    (by dsimp;omega) (by simp) ε₀]
  simpa only [regrade_comp,regrade_precomp,←Category.assoc,eqToHom_trans] using
    zero_h_shifted_first_unshift T (s+1) t z u hu ε₀ hε₀

/-- The actual positive-g May source retains its ordinary h₂ label,
its first quotient, and the corresponding finite-cycle qualification. -/
private theorem positive_g_may_source_first_label
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle model T he).obj₃ q))
    (d : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1)
    (hd : d ≫ (model.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ q) :
    let dNu := homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
      (quotientShiftDesuspend T.X (1,0) N εN (t-s) t
        (d ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
    dNu ≫ (model.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X (s+1) t u ∧
    Detects (model.convergence (.quotient N (.nu T.X))) (s+1,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model T.X N (s+1) t 0 u)) dNu ∧
    IsCycle model T.X N (s+1,t) u := by
  dsimp only
  let E := normalizedSuspensionZeroIso T he hf
  let EZ := normalizedThirdNegativeIso T he hg
  let V := normalizedTriangle model T he
  have hfirst : d ≫ (model.quotients.tower _).rho 1 N (by omega) =
      (homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫ XModLambdaN.map EZ.inv 1) ≫
        XModLambdaN.map V.mor₃ 1 := by
    rw [←(model.quotients.tower _).rho_comp (show 1≤q by omega) hqN,
      ←Category.assoc,hd,Category.assoc,
      ←(model.quotients.natural V.mor₃).rho_naturality hq,←Category.assoc,ha]
  have hj : (d ≫ XModLambdaN.map E.hom N) ≫ (model.quotients.tower _).rho 1 N (by omega) =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫ XModLambdaN.map (zeroHShiftedRaw T) 1 := by
    rw [Category.assoc,←(model.quotients.natural E.hom).rho_naturality (show 1≤N by omega),
      ←Category.assoc,hfirst]
    simp only [Category.assoc]
    rw [←model.quotients.functoriality.map_comp,normalized_third_arrow_positive_g T he hf hg hh,
      ←model.quotients.functoriality.map_comp]
    simp only [EZ,Iso.inv_hom_id_assoc]
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) 1
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hr := quotient_shift_desuspend_restriction T.X (1,0) 1 N (by omega) (by omega)
    ε₁ εN hε₁ hεN (t-s) t _ _ hj
  have hr' := congrArg (homotopyRegrade (show (t-s)-1=t-(s+1) by omega)
    (show t-0=t by omega)) hr
  rw [regrade_comp,positive_g_first_desuspend T s t z u hu ε₁ hε₁] at hr'
  exact ⟨hr',first_label_detects_unshifted T.X N (by omega) (s+1) t u _ hr',
    specified_adjacent_lift_cycles T.X N (by omega) (s+1) t u _ hr'⟩

/-- The same positive-g May source at level c.  Finite-cycle membership
of the original classical source is retained together with the detector. -/
private theorem positive_g_may_source_at_level
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (c q K : ℕ) (hq : 0<q) (hqK : q≤K) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u))
    (εK : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) K ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) K))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hεK : XModLambdaN.incl _ K ≫ εK.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ K))
    (hεN : XModLambdaN.incl _ (c+K) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+K)))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle model T he).obj₃ q))
    (d : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) K))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1)
    (hd : d ≫ (model.quotients.tower _).rho q K hqK =
      a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ q) :
    IsCycle model T.X K (s+1,t) u ∧
    Detects (model.convergence (.quotient (c+K) (.nu T.X))) (s+1,t,t-c)
      (finiteTargetLabel model T.X (c+K) (s+1) t c u)
      (positiveHSourceDesuspend T he hf (c+K) c s t εN
        (finiteCoefficientInsert _ c K (by omega) (t-s) t d)) := by
  have H := positive_g_may_source_first_label T he hf hg hh q K hq hqK s t z u hu
    εK hεK a d ha hd
  exact ⟨H.2.2,positive_h_coefficient_source_detects T he hf c K (by omega) s t u
    εK εN hεK hεN d H.2.1⟩


/-- Changing the two source indices commutes with the actual positive
first-quotient operation. -/
private theorem positive_first_quotient_operation_regrade
    (Y Z : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Z.obj model.auxiliary))
    (s t s' t' : ℤ) (hs : s=s') (ht : t=t')
    (v : Ambient model Y (s,t)) :
    positiveFirstQuotientOperation Y Z F s' t'
      (positiveClassicalRegrade (Prod.ext hs ht) v) =
    positiveClassicalRegrade
      (Prod.ext (congrArg (fun a : ℤ => a+1) hs)
        (congrArg (fun a : ℤ => a+1) ht))
      (positiveFirstQuotientOperation Y Z F s t v) := by
  subst s'
  subst t'
  rfl

private theorem positive_classical_regrade_trans
    (X : ClassicalObject) {p q r : ℤ×ℤ} (hpq : p=q) (hqr : q=r)
    (x : Ambient model X p) :
    positiveClassicalRegrade hqr (positiveClassicalRegrade hpq x) =
      positiveClassicalRegrade (hpq.trans hqr) x := by
  subst q
  subst r
  rfl

/-- A genuine differential is unchanged by transporting its specified
E₂ target along a degree equality. -/
private theorem positive_has_differential_target_regrade
    (X : ClassicalObject) (r : ℤ) (p q q' : ℤ×ℤ) (hq : q=q')
    (x : Ambient model X p) (y : Ambient model X q)
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary)) r p q x y) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary)) r p q' x
      (positiveClassicalRegrade hq y) := by
  subst q'
  exact hd



private theorem bi_susp_symm_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (q : ℤ)
    (a : BiHom (m-1) (w+q) A) :
    homotopyRegrade hm hw ((biSuspensionHomEquiv m w q A).symm a) =
      (biSuspensionHomEquiv m' w' q A).symm
        (homotopyRegrade (by omega) (by omega) a) := by
  subst m'; subst w'; rfl

/-- Original classical positive-g inputs construct a specified May
representative at every finite coefficient level, retaining the source cycle. -/
private theorem positive_g_classical_second_may_at_level
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1))))
    (hεN : XModLambdaN.incl _ (c+(q+1)) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1)))) :
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    IsCycle model T.X (q+1) (s+1,t) u ∧
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) := by
  dsimp only
  let V := normalizedTriangle model T he
  let v' : Ambient model T.Y ((s+1)+q,(t+1)+q-1) :=
    positiveClassicalRegrade (Prod.ext (by omega) (by omega)) v
  have hd' : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+1,t+1) ((s+1)+q+1,(t+1)+q) z
      (positiveClassicalRegrade (X:=T.Z) (Prod.ext (by omega) (by omega))
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
          ((s+1)+q) ((t+1)+q-1) v')) := by
    dsimp only [v']
    rw [positive_first_quotient_operation_regrade T.Y T.Z (normalizedSecondPositiveMap T hg)
      (s+q+1) (t+q) ((s+1)+q) ((t+1)+q-1) (by omega) (by omega),
      positive_classical_regrade_trans]
    exact positive_has_differential_target_regrade T.Z _ _ _ _ _ z _ hd
  obtain ⟨a₀,d₀,ha₀,_,hd₀,hf₀⟩ := positive_second_differential_may
    T he hT hg q hq (s+1) (t+1) z v' hd' ey hey
  let a := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) a₀
  let d := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) d₀
  have ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) ha₀
    simpa only [a,regrade_comp,regrade_transitive] using h
  have hdR : d ≫ (model.quotients.tower _).rho q (q+1) (by omega) =
      a ≫ XModLambdaN.map V.mor₃ q := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hd₀
    simpa only [a,d,regrade_comp] using h
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) (q+1)
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hs := positive_g_may_source_at_level T he hf hg hh c q (q+1) hq (by omega)
    s t z u hu εn εN hεn hεN a d ha hdR
  refine ⟨hs.1,finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t d,hs.2,?_⟩
  rw [finite_coefficient_insert_natural]
  congr 1
  apply (cancel_mono ey.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega)) hf₀
  have hv : nativeFirstLabel T.Y ((s+1)+q) ((t+1)+q-1) v' =
      homotopyRegrade (by omega) (by omega)
        (nativeFirstLabel T.Y (s+q+1) (t+q) v) :=
    native_first_label_transport T.Y (show s+q+1=(s+1)+q by omega)
      (show t+q=(t+1)+q-1 by omega) v
  rw [hv] at h
  simpa only [regrade_comp,output_regrade_neg,bi_susp_symm_regrade,
    regrade_transitive] using h

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
