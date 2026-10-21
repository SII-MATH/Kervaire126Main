module
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.GeneralizedMahowald.HTarget
import all KIP126.ProofTools.GeneralizedMahowald.FSourceRegrade
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
/-! The positive connecting-exponent branch uses the actual normalized
h first-quotient operation. Its source labels are transported through the
chosen positive-weight and classical-suspension comparisons, retaining the
same finite May representative and signed target. -/

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

private def positiveHMap (T : TriangleData model.auxiliary)
    (hh : normalizedExponent model.classicalTower T.h=1) :
    (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (T.Z.obj model.auxiliary)) ⟶
      model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary) := by
  simpa only [hh,Nat.cast_one] using (model.normalizedMap T.Z (.shift 1 T.X) T.h).map

private def positiveHNativeRaw (T : TriangleData model.auxiliary)
    (hh : normalizedExponent model.classicalTower T.h=1) :
    model.nu.functor.obj (T.Z.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift (1,0)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  negativeLift 1 (positiveHMap T hh) ≫
    (SyntheticCategory.biShift (0,-1)).map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom ≫
    (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).hom.app _

private theorem positive_h_native_raw_shift (T : TriangleData model.auxiliary)
    (hh : normalizedExponent model.classicalTower T.h=1) :
    (SyntheticCategory.biShift (0,1)).map (positiveHNativeRaw T hh) ≫
      (biShiftAddIso (1,0) (0,1) (1,1) (by decide)).hom.app _ =
    positiveHMap T hh ≫ (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom := by
  exact shift_negativeLift_target 1 (1,1) (1,0) (by decide) (by decide) _ _

private def normalizedSuspensionZeroIso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0) :
    ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (1,0)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    (zero_positive_iso (model.nu.functor.obj (T.X.obj model.auxiliary)) _ hf) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _

private theorem normalized_third_arrow_positive (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=1) :
    (normalizedTriangle model T he).mor₃ ≫ (normalizedSuspensionZeroIso T he hf).hom =
      (normalizedThirdZeroIso T he hg).hom ≫ positiveHNativeRaw T hh := by
  have H := raw_connecting_zero_zero_one _ _ _ he hf hg hh
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (model.nu.suspensionIso (T.X.obj model.auxiliary))
  have H' := congrArg (fun z => z ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) H
  have hn (k : ℕ) (hk : k=1) {A B : SyntheticSpectrum}
      (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
      negative_lift_at_one k hk f = negativeLift 1
        ((congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A ⟶ B) hk).mp f) := by
    subst k
    rfl
  rw [hn] at H'
  simp only [Category.assoc] at H'
  erw [Iso.hom_inv_id_app,Category.comp_id] at H'
  simpa only [normalizedTriangle,Triangle.mk,normalizedConnecting,raw_normalized_connecting,
    normalizedSuspensionZeroIso,normalizedThirdZeroIso,positiveHNativeRaw,positiveHMap,
    negative_lift_at_one,zero_negative_iso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,eqToIso.hom,biShiftAddIso,eqToIso_refl,Iso.trans_refl,
    Category.assoc,Iso.hom_inv_id_app,Category.comp_id] using H'

private theorem quotient_unshift_regrade_pair (X : ClassicalObject) (δ p p' : ℤ×ℤ)
    (hp : p=p') (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    homotopyRegrade (congrArg Prod.fst hp) (congrArg Prod.snd hp)
      (quotientUnshift X δ p q ε a) =
    quotientUnshift X δ p' q ε
      (homotopyRegrade (congrArg (fun v => (v+δ).1) hp)
        (congrArg (fun v => (v+δ).2) hp) a) := by
  subst p'
  rfl

private theorem positive_h_first_desuspend (T : TriangleData model.auxiliary)
    (hh : normalizedExponent model.classicalTower T.h=1) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (εδ : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hεδ : XModLambdaN.incl _ 1 ≫ εδ.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
      (quotientShiftDesuspend T.X (1,0) 1 εδ (t-s) t
        (nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (positiveHNativeRaw T hh) 1)) =
    nativeFirstLabel T.X (s+1) t u := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨εh,hεh,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
    (model.nu.functor.obj (T.Z.obj model.auxiliary))
  obtain ⟨εσ,hεσ,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) 1
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hback : shiftHomotopyClass (0,1) (t-s,t) (nativeFirstLabel T.Z s t z) ≫ εh.inv =
      homotopyRegrade (by simp) rfl ((model.firstQuotient T.Z 1 s t).symm z) := by
    have h := firstQuotient_positive_shift T.Z s t z εh hεh
    rw [←first_label_inline] at h
    have h' := congrArg (homotopyRegrade (show t-s=((t-s,t)+(0,1)).1 by simp) rfl) h
    simpa only [nativeFirstLabel,regrade_comp,regrade_precomp,←Category.assoc,
      eqToHom_trans,eqToHom_refl,Category.id_comp] using h'
  have H := quotient_h_target_representative T.X T.Z 1 1 (by omega) (by omega)
    (1,0) (by decide) (positiveHMap T hh) (positiveHNativeRaw T hh)
    (positive_h_native_raw_shift T hh) εh εδ εσ hεh hεδ hεσ
    (t-s) t (nativeFirstLabel T.Z s t z) _ hback
  have hl := positive_first_quotient_native_label T.Z (.shift 1 T.X)
    (positiveHMap T hh) s t z
  have hs := suspension_first_unshift T.X (s+1) t u _ εσ hεσ hu
  have Hr := congrArg (homotopyRegrade (show t-s-1=t-(s+1) by omega)
    (show t-0=t by omega)) H.symm
  exact Hr.trans (by
    change quotientUnshift T.X (1,1) (t-(s+1),t) 1 εσ _ = nativeFirstLabel T.X (s+1) t u at hs
    simp only [nativeFirstLabel] at hl
    erw [hl] at hs
    rw [quotient_unshift_regrade_pair T.X (1,1) (t-s-1,t-0) (t-(s+1),t)
      (by ext <;> dsimp <;> omega)]
    simpa only [regrade_comp,regrade_precomp,←Category.assoc,eqToHom_trans] using hs)

/-- The raw May source in the positive h branch has the prescribed h₁
label after its actual ordinary-suspension deshift. -/
private theorem positive_h_may_source_first_label
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=1)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle model T he).obj₃ q))
    (c : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hc : c ≫ (model.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ q) :
    let cNu := homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
      (quotientShiftDesuspend T.X (1,0) N εN (t-s) t
        (c ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
    cNu ≫ (model.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X (s+1) t u ∧
    Detects (model.convergence (.quotient N (.nu T.X))) (s+1,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model T.X N (s+1) t 0 u)) cNu ∧
    IsCycle model T.X N (s+1,t) u := by
  dsimp only
  let E := normalizedSuspensionZeroIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let V := normalizedTriangle model T he
  have hfirst : c ≫ (model.quotients.tower _).rho 1 N (by omega) =
      (nativeFirstLabel T.Z s t z ≫ XModLambdaN.map EZ.inv 1) ≫
        XModLambdaN.map V.mor₃ 1 := by
    rw [←(model.quotients.tower _).rho_comp (show 1≤q by omega) hqN,
      ←Category.assoc,hc,Category.assoc,
      ←(model.quotients.natural V.mor₃).rho_naturality hq,←Category.assoc,ha]
  have hj : (c ≫ XModLambdaN.map E.hom N) ≫ (model.quotients.tower _).rho 1 N (by omega) =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (positiveHNativeRaw T hh) 1 := by
    rw [Category.assoc,←(model.quotients.natural E.hom).rho_naturality (show 1≤N by omega),
      ←Category.assoc,hfirst]
    simp only [Category.assoc]
    rw [←model.quotients.functoriality.map_comp,normalized_third_arrow_positive T he hf hg hh,
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
  rw [regrade_comp,positive_h_first_desuspend T hh s t z u hu ε₁ hε₁] at hr'
  exact ⟨hr',first_label_detects_unshifted T.X N (by omega) (s+1) t u _ hr',
    specified_adjacent_lift_cycles T.X N (by omega) (s+1) t u _ hr'⟩

/-- The positive-h branch consumes the classical second differential and
the actual h₁ label. The same May representative carries that source label
and the signed prescribed target, without any extension premise. -/
private theorem positive_h_classical_second_may
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (q+1) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (q+1)))
    (hεN : XModLambdaN.incl _ (q+1) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (q+1))) :
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ a : BiHom (t-s) t (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (q+1)),
      Detects (model.convergence (.quotient (q+1) (.nu T.X))) (s+1,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model T.X (q+1) (s+1) t 0 u))
        (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
          (quotientShiftDesuspend T.X (1,0) (q+1) εN (t-s) t
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom (q+1)))) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (q+1) ≫
        ey.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
  dsimp only
  obtain ⟨a,c,ha,_,hc,himage⟩ := classical_second_differential_may T he hT hg q hq s t z v hd ey hey
  have hsource := positive_h_may_source_first_label T he hf hg hh q (q+1) hq (by omega)
    s t z u hu εN hεN a c ha hc
  exact ⟨c,hsource.2.1,himage⟩

private theorem finite_coefficient_shift_bigraded_all
    (X : ClassicalObject) (δ : ℤ×ℤ) (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (N-c) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (εN : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hεn : XModLambdaN.incl _ (N-c)≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (N-c)))
    (hεN : XModLambdaN.incl _ N≫εN.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ N))
    (b : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c))) :
    homotopyRegrade (m':=m+δ.1) (w':=w+δ.2-c) rfl (by dsimp; omega)
        (shiftHomotopyClass δ (m,w-c) (finiteCoefficientShiftClass _ N c hcN m w b)) ≫ εN.inv =
      finiteCoefficientShiftClass _ N c hcN (m+δ.1) (w+δ.2)
        (shiftHomotopyClass δ (m,w) b ≫ εn.inv) := by
  by_cases hc : c=0
  · subst c
    simp only [Nat.sub_zero] at εn hεn b
    have heq := shifted_quotient_sphere_congruence X X δ N N (by omega) le_rfl
      εn hεn εn.hom εN.hom (hεn.trans hεN.symm) (m+δ.1) (w+δ.2)
      (shiftHomotopyClass δ (m,w) b≫εn.inv)
    have heq' := congrArg (fun z => z≫εN.inv) heq
    simp only [Category.assoc,Iso.inv_hom_id,Iso.hom_inv_id,Category.comp_id] at heq'
    simpa only [finiteCoefficientShiftClass,↓reduceDIte,coefficient_shift_input_regrade,
      ←regrade_comp,output_regrade_trans] using
      congrArg (homotopyRegrade rfl (show w+δ.2=w+δ.2-(0:ℕ) by simp)) heq'
  · exact finite_coefficient_shift_bigraded X δ N c (by omega) hcN m w
      εn εN hεn hεN b

private theorem finite_coefficient_shift_desuspend
    (X : ClassicalObject) (δ : ℤ×ℤ) (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (N-c) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (εN : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hεn : XModLambdaN.incl _ (N-c)≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (N-c)))
    (hεN : XModLambdaN.incl _ N≫εN.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ N))
    (a : BiHom (m+δ.1) (w+δ.2) (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (N-c))) :
    quotientUnshift X δ (m,w-c) N εN
      (homotopyRegrade rfl (show w+δ.2-c=((m,w-c)+δ).2 by dsimp; omega)
        (finiteCoefficientShiftClass _ N c hcN (m+δ.1) (w+δ.2) a)) =
      finiteCoefficientShiftClass _ N c hcN m w
        (quotientUnshift X δ (m,w) (N-c) εn a) := by
  have H := finite_coefficient_shift_bigraded_all X δ N c hcN m w εn εN hεn hεN
    (quotientUnshift X δ (m,w) (N-c) εn a)
  rw [shift_quotient_unshift] at H
  have H' := congrArg (homotopyRegrade rfl
    (show w+δ.2-c=((m,w-c)+δ).2 by dsimp; omega)) H
  simp only [←regrade_comp,output_regrade_trans] at H'
  have regrade_self {A : SyntheticSpectrum} {m w : ℤ}
      (hm : m=m) (hw : w=w) (b : BiHom m w A) : homotopyRegrade hm hw b=b := rfl
  simp only [regrade_self] at H'
  rw [←H',quotient_unshift_shift]

private theorem finite_coefficient_insert_desuspend
    (X : ClassicalObject) (δ : ℤ×ℤ) (c K : ℕ) (hK : 0<K) (m w : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) K ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K))
    (εN : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K)))
    (hεn : XModLambdaN.incl _ K≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ K))
    (hεN : XModLambdaN.incl _ (c+K)≫εN.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (c+K)))
    (a : BiHom (m+δ.1) (w+δ.2) (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) K)) :
    quotientUnshift X δ (m,w-c) (c+K) εN
      (homotopyRegrade rfl (show w+δ.2-c=((m,w-c)+δ).2 by dsimp; omega)
        (finiteCoefficientInsert _ c K hK (m+δ.1) (w+δ.2) a)) =
      finiteCoefficientInsert _ c K hK m w
        (quotientUnshift X δ (m,w) K εn a) := by
  have hi (n : ℕ) (hn : n=K)
      (he : (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) K ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K)) =
        (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) n ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n))) :
      XModLambdaN.incl _ n≫(he.mp εn).hom =
        (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ n) := by
    subst n
    exact hεn
  have H := finite_coefficient_shift_desuspend X δ (c+K) c (by omega) m w
    (by simpa only [Nat.add_sub_cancel_left] using εn) εN
    (hi (c+K-c) (by omega) _) hεN
    (by simpa only [Nat.add_sub_cancel_left] using a)
  unfold finiteCoefficientInsert
  convert H using 1
  apply congrArg (finiteCoefficientShiftClass _ (c+K) c (by omega) m w)
  have ht (n : ℕ) (hn : n=K)
      (he : (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) K ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K)) =
        (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) n ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)))
      (ha : BiHom (m+δ.1) (w+δ.2) (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) K) =
        BiHom (m+δ.1) (w+δ.2) (XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) n))
      (hb : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K) =
        BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)) :
      hb.mp (quotientUnshift X δ (m,w) K εn a) =
        quotientUnshift X δ (m,w) n (he.mp εn) (ha.mp a) := by
    subst n
    rfl
  exact ht (c+K-c) (by omega) _ _ _

private theorem finite_coefficient_insert_regrade
    (A : SyntheticSpectrum) (c K : ℕ) (hK : 0<K)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w (XModLambdaN A K)) :
    finiteCoefficientInsert A c K hK m' w' (homotopyRegrade hm hw a) =
      homotopyRegrade hm (congrArg (fun v : ℤ => v-(c:ℤ)) hw)
        (finiteCoefficientInsert A c K hK m w a) := by
  subst m'; subst w'; rfl

private def positiveHSourceDesuspend
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N c : ℕ) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (a : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
    BiHom (t-(s+1)) (t-c) (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N) :=
  quotientUnshift T.X (1,0) (t-(s+1),t-c) N ε
    (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))

private theorem positive_h_coefficient_source_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (c K : ℕ) (hK : 0<K) (s t : ℤ) (u : Ambient model T.X (s+1,t))
    (εn : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) K ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) K))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hεn : XModLambdaN.incl _ K ≫ εn.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ K))
    (hεN : XModLambdaN.incl _ (c+K) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+K)))
    (a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) K))
    (ha : Detects (model.convergence (.quotient K (.nu T.X))) (s+1,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model T.X K (s+1) t 0 u))
      (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-0=t by omega)
        (quotientShiftDesuspend T.X (1,0) K εn (t-s) t
          (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom K)))) :
    Detects (model.convergence (.quotient (c+K) (.nu T.X))) (s+1,t,t-c)
      (finiteTargetLabel model T.X (c+K) (s+1) t c u)
      (positiveHSourceDesuspend T he hf (c+K) c s t εN
        (finiteCoefficientInsert _ c K hK (t-s) t a)) := by
  erw [quotient_shift_desuspend_as_native_unshift T.X (1,0) (t-(s+1),t) K (t-s) t
    (by dsimp; omega) (by simp) εn] at ha
  have hd := finite_coefficient_insert_detects T.X c K hK (s+1) t u _ ha
  have heq := finite_coefficient_insert_desuspend T.X (1,0) c K hK (t-(s+1)) t
    εn εN hεn hεN
    (homotopyRegrade (show t-s=(t-(s+1))+(1,0).1 by dsimp; omega)
      (show t=t+(1,0).2 by simp)
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom K))
  have heq' : positiveHSourceDesuspend T he hf (c+K) c s t εN
        (finiteCoefficientInsert _ c K hK (t-s) t a) =
      finiteCoefficientInsert _ c K hK (t-(s+1)) t
        (quotientUnshift T.X (1,0) (t-(s+1),t) K εn
          (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom K))) := by
    erw [finite_coefficient_insert_regrade] at heq
    simpa only [positiveHSourceDesuspend,finite_coefficient_insert_natural,
      regrade_precomp,←Category.assoc,eqToHom_trans] using heq
  rw [heq']
  exact hd

/-- The same positive-h May representative at every finite level. -/
private theorem positive_h_classical_second_may_at_level
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 0)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
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
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) := by
  dsimp only
  let V := normalizedTriangle model T he
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) (q+1)
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  obtain ⟨m₀,hs,hf₀⟩ := positive_h_classical_second_may T he hT hf hg hh q hq s t z u v hu hd
    ey hey εn hεn
  let m := finiteCoefficientInsert (V.obj₁⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t m₀
  refine ⟨m,?_,?_⟩
  · exact positive_h_coefficient_source_detects T he hf c (q+1) (by omega) s t u
      εn εN hεn hεN m₀ hs
  · dsimp only [m]
    rw [finite_coefficient_insert_natural]
    congr 1
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hf₀

/-- The common core's source cycle qualification follows from the same
classical inputs, before passing to a coefficient layer. -/
private theorem positive_h_classical_second_cycles
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v)) :
    IsCycle model T.X (q+1) (s+1,t) u := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he hT (q+1) (by omega)
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) (q+1)
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  obtain ⟨a,c,ha,_,hc,_⟩ := classical_second_differential_may T he hT hg q hq s t z v hd ey hey
  exact (positive_h_may_source_first_label T he hf hg hh q (q+1) hq (by omega)
    s t z u hu ε hε a c ha hc).2.2

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
