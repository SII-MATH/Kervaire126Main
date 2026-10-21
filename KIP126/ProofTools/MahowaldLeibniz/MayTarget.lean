module

import all KIP126.ProofTools.MahowaldLeibniz.CoefficientShift
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison

/-! Actual suspension coordinates and finite labels of the signed May target. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- In vertical coordinates the coefficient insertion is literally the
selected lambda map; this fixes the representative before suspending it. -/
private theorem finite_coefficient_shift_vertical
    (A : SyntheticSpectrum) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
    (a : BiHom m (w+c) (XModLambdaN A (N-c))) :
    homotopyRegrade rfl (show (w+c)-c=w by omega)
      (finiteCoefficientShiftClass A N c hcN m (w+c) a) =
      vertical_hom m w c (XModLambdaN A (N-c)) a ≫
        ((model.quotients.tower A).triangle hc hcN).lambdaMap := by
  simp only [finiteCoefficientShiftClass,show c≠0 by omega,↓reduceDIte,
    regrade_comp,output_regrade_trans]
  congr 1
  simpa [shiftHomotopyClass,susp_invariance,Iso.homCongr,vertical_hom] using
    susp_regrade_eq m (w+c) 0 (-(c:ℤ)) m w (by omega) (by omega)
      (XModLambdaN A (N-c)) a

/-- The actual signed May target is the ordinary suspension of the same
coefficient-inserted class.  No equality of unrelated quotient choices is used. -/
private theorem finite_coefficient_shift_suspended_target
    (A : SyntheticSpectrum) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
    (a : BiHom (m-1) (w+c) (XModLambdaN A (N-c))) :
    (biSuspensionHomEquiv m w c (XModLambdaN A (N-c))).symm a ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((model.quotients.tower A).triangle hc hcN).lambdaMap ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      homotopyRegrade (show (m-1)+1=m by omega) (by simp)
        (shiftHomotopyClass (1,0) (m-1,w)
          (homotopyRegrade rfl (show (w+c)-c=w by omega)
            (finiteCoefficientShiftClass A N c hcN (m-1) (w+c) a))) := by
  rw [finite_coefficient_shift_vertical A N c hc hcN]
  rw [bi_susp_symm_vertical model.quotients.coherence]
  simp only [Category.assoc]
  erw [←Functor.map_comp_assoc]
  erw [←(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app,Category.comp_id]
  simpa [shiftHomotopyClass,susp_invariance,Iso.homCongr] using
    (susp_regrade_eq (m-1) w 1 0 m w (by omega) (by omega) (XModLambdaN A N)
      (vertical_hom (m-1) w c (XModLambdaN A (N-c)) a ≫
        ((model.quotients.tower A).triangle hc hcN).lambdaMap)).symm

/-- The native representative corresponding to the signed actual May output. -/
private def finiteMayNativeTargetClass (A : SyntheticSpectrum)
    (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (a : BiHom (m-1) (w+c) (XModLambdaN A (N-c))) :
    BiHom (m-1) w (XModLambdaN A N) :=
  -homotopyRegrade rfl (show (w+c)-c=w by omega)
    (finiteCoefficientShiftClass A N c hcN (m-1) (w+c) a)

/-- This identity preserves the actual minus sign on homotopy classes. -/
private theorem finite_may_signed_target_eq_suspension
    (A : SyntheticSpectrum) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
    (a : BiHom (m-1) (w+c) (XModLambdaN A (N-c))) :
    (-(biSuspensionHomEquiv m w c (XModLambdaN A (N-c))).symm a ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((model.quotients.tower A).triangle hc hcN).lambdaMap) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      homotopyRegrade (show (m-1)+1=m by omega) (by simp)
        (shiftHomotopyClass (1,0) (m-1,w)
          (finiteMayNativeTargetClass A N c hcN m w a)) := by
  have h := congrArg Neg.neg (finite_coefficient_shift_suspended_target A N c hc hcN m w a)
  simpa only [Category.assoc,finiteMayNativeTargetClass,Preadditive.neg_comp,shiftHomotopyClass,
    Functor.map_neg,Preadditive.comp_neg,output_regrade_neg] using h

private theorem coefficient_shift_regrade (A : SyntheticSpectrum)
    (N c : ℕ) (hcN : c<N) {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w (XModLambdaN A (N-c))) :
    finiteCoefficientShiftClass A N c hcN m' w' (homotopyRegrade hm hw a) =
      homotopyRegrade hm (congrArg (fun v : ℤ => v-c) hw)
        (finiteCoefficientShiftClass A N c hcN m w a) := by
  subst m'
  subst w'
  rfl

/-- The signed native output detects the prescribed classical target at
layer c.  Its sign is removed only on the classical Adams label. -/
private theorem finite_may_native_target_detects
    (X : ClassicalObject) (N c : ℕ) (hcN : c<N) (m w s t : ℤ)
    (hm : m-1=t-s) (hw : w+c=t)
    (x : Ambient model X (s,t))
    (a : BiHom (m-1) (w+c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (ha : Detects (model.convergence (.quotient (N-c) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (N-c) s t 0 x))
      (homotopyRegrade hm hw a)) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,t-c)
      (finiteTargetLabel model X N s t c x)
      (homotopyRegrade hm (show w=t-c by omega)
        (finiteMayNativeTargetClass _ N c hcN m w a)) := by
  have hd := finite_coefficient_shift_detects X N c hcN s t t (by omega) x
    (homotopyRegrade hm hw a) (by rw [zero_weight_label]; exact ha)
  rw [finite_coefficient_weight_label] at hd
  have hn := finite_target_detects_neg X N s t c x _ hd
  rw [coefficient_shift_regrade] at hn
  convert hn using 1
  simp only [finiteMayNativeTargetClass,output_regrade_neg,output_regrade_trans]

private theorem finite_coefficient_shift_bigraded
    (X : ClassicalObject) (δ : ℤ×ℤ) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
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
  apply (cancel_mono εN.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  simp only [finiteCoefficientShiftClass,show c≠0 by omega,↓reduceDIte]
  rw [shift_hom_comp,regrade_comp,shift_hom_comp,regrade_comp]
  simp only [Category.assoc]
  rw [quotient_shift_lambda_on_spheres X δ N c hc hcN εn εN hεn hεN]
  rw [shift_regrade,shift_regrade,shift_regrade]
  simp only [shiftHomotopyClass]
  rw [←Category.assoc]
  apply congrArg (fun z => z ≫ (SyntheticCategory.biShift δ).map
    ((model.quotients.tower _).triangle hc hcN).lambdaMap)
  simpa [biShiftAddIso,Category.assoc] using
    (shift_hom_swap (m,w) δ (0,-(c:ℤ)) (m+δ.1,w+δ.2) (m,w-c)
      (m+δ.1,w+δ.2-c)
      rfl (by ext <;> simp [sub_eq_add_neg])
      (by ext <;> simp [sub_eq_add_neg]) (by ext <;> dsimp; omega) b).symm

private def ordinaryQuotientToBigraded (X : ClassicalObject) (N : ℕ)
    (e : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧) :
    XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) :=
  (model.quotients.functoriality.functor N).mapIso
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app _) ≪≫
      e ≪≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _

private theorem ordinary_quotient_to_bigraded_incl (X : ClassicalObject) (N : ℕ)
    (e : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl _ N≫e.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N)) :
    XModLambdaN.incl _ N≫(ordinaryQuotientToBigraded X N e).hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N) := by
  simp only [ordinaryQuotientToBigraded,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
    Functor.mapIso_hom,LambdaQuotientFunctoriality.functor]
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc (XModLambdaN.incl _ N),he,
    ←(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app,Category.comp_id]

/-- Ordinary-suspension form of coefficient insertion, using the specified
inclusion-compatible quotient coordinates at both lengths. -/
private theorem finite_coefficient_shift_ordinary_positive
    (X : ClassicalObject) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (N-c)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (N-c)))
    (heN : XModLambdaN.incl _ N≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (m+1) (w+0)
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c)))
    (b : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (hab : a≫en.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      shiftHomotopyClass (1,0) (m,w) b) :
    finiteCoefficientShiftClass _ N c hcN (m+1) (w+0) a ≫ eN.hom ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      homotopyRegrade (m':=m+1) (w':=w+0-c) rfl (by dsimp; omega)
        (shiftHomotopyClass (1,0) (m,w-c)
          (finiteCoefficientShiftClass _ N c hcN m w b)) := by
  let εn := ordinaryQuotientToBigraded X (N-c) en
  let εN := ordinaryQuotientToBigraded X N eN
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hsource : shiftHomotopyClass (1,0) (m,w) b≫εn.inv =
      a≫XModLambdaN.map (κ.inv.app A) (N-c) := by
    rw [←hab]
    simp only [εn,ordinaryQuotientToBigraded,Iso.trans_inv,Iso.app_inv,Iso.symm_inv,
      Functor.mapIso_inv,LambdaQuotientFunctoriality.functor,Category.assoc,
      Iso.inv_hom_id_app_assoc,Iso.hom_inv_id_assoc,κ,A]
  have h := finite_coefficient_shift_bigraded X (1,0) N c hc hcN m w εn εN
    (ordinary_quotient_to_bigraded_incl X (N-c) en hen)
    (ordinary_quotient_to_bigraded_incl X N eN heN) b
  rw [hsource,←finite_coefficient_shift_natural] at h
  have h' := congrArg (fun z => z≫εN.hom) h
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h'
  simp only [εN,ordinaryQuotientToBigraded,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
    Functor.mapIso_hom,LambdaQuotientFunctoriality.functor,κ,A] at h'
  rw [←Category.assoc (XModLambdaN.map _ N),←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app,model.quotients.functoriality.map_id,Category.id_comp] at h'
  exact h'.symm

private theorem coefficient_shift_input_regrade (δ : ℤ×ℤ) {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    shiftHomotopyClass δ (m',w') (homotopyRegrade hm hw a) =
      homotopyRegrade (congrArg (fun n => n+δ.1) hm)
        (congrArg (fun n => n+δ.2) hw) (shiftHomotopyClass δ (m,w) a) := by
  subst m'; subst w'; rfl

private theorem finite_coefficient_shift_ordinary
    (X : ClassicalObject) (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (N-c)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (N-c)))
    (heN : XModLambdaN.incl _ N≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (m+1) (w+0)
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c)))
    (b : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (hab : a≫en.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      shiftHomotopyClass (1,0) (m,w) b) :
    finiteCoefficientShiftClass _ N c hcN (m+1) (w+0) a ≫ eN.hom ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      homotopyRegrade (m':=m+1) (w':=w+0-c) rfl (by dsimp; omega)
        (shiftHomotopyClass (1,0) (m,w-c)
          (finiteCoefficientShiftClass _ N c hcN m w b)) := by
  by_cases hc : c=0
  · subst c
    simp only [Nat.sub_zero] at en hen a b hab
    have heq := finite_nu_suspension_comparisons_equal_on_spheres X N (by omega)
      en eN hen heN (m+1) (w+0) a
    have hN : a≫eN.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
        shiftHomotopyClass (1,0) (m,w) b := by
      rw [←Category.assoc,←heq,Category.assoc]
      exact hab
    simpa only [finiteCoefficientShiftClass,↓reduceDIte,coefficient_shift_input_regrade,
      ←regrade_comp,output_regrade_trans] using
      congrArg (homotopyRegrade rfl (show w+0=w+0-(0:ℕ) by simp)) hN
  · exact finite_coefficient_shift_ordinary_positive X N c (by omega) hcN m w
      en eN hen heN a b hab

/-- Coefficient insertion commutes with ordinary suspension in the exact
coordinates used by the finite normalized boundary square. -/
private theorem finite_coefficient_shift_ordinary_representative
    (X : ClassicalObject) (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (N-c)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (N-c)))
    (heN : XModLambdaN.incl _ N≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom m w
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (N-c)))
    (b : BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (hab : a≫en.hom=ordinarySuspendedRepresentative _ m w b) :
    finiteCoefficientShiftClass _ N c hcN m w a ≫ eN.hom =
      ordinarySuspendedRepresentative _ m (w-c)
        (finiteCoefficientShiftClass _ N c hcN (m-1) w b) := by
  have hab' : homotopyRegrade (show m=(m-1)+1 by omega) (show w=w+0 by omega) a ≫
      en.hom ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ =
      shiftHomotopyClass (1,0) (m-1,w) b := by
    rw [←regrade_comp,←Category.assoc a,hab]
    simp only [ordinarySuspendedRepresentative,Category.assoc,Iso.hom_inv_id_app,
      Category.comp_id,output_regrade_trans]
    rfl
  have h := finite_coefficient_shift_ordinary X N c hcN (m-1) w en eN hen heN _ b hab'
  rw [coefficient_shift_regrade] at h
  have h' := congrArg (homotopyRegrade (show (m-1)+1=m by omega)
    (show w+0-c=w-c by omega)) h
  simp only [←regrade_comp,output_regrade_trans] at h'
  have regrade_self {A : SyntheticSpectrum} {m w : ℤ}
      (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a=a := rfl
  apply (cancel_mono ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)).mp
  simpa only [ordinarySuspendedRepresentative,Category.assoc,Iso.hom_inv_id_app,
    Category.comp_id,regrade_self] using h'

private theorem finite_coefficient_insert_ordinary_representative
    (X : ClassicalObject) (c K : ℕ) (hK : 0<K) (m w : ℤ)
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) K ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K)⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+K) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K))⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ K≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ K))
    (heN : XModLambdaN.incl _ (c+K)≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+K)))
    (a : BiHom m w
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) K))
    (b : BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K))
    (hab : a≫en.hom=ordinarySuspendedRepresentative _ m w b) :
    finiteCoefficientInsert _ c K hK m w a ≫ eN.hom =
      ordinarySuspendedRepresentative _ m (w-c)
        (finiteCoefficientInsert _ c K hK (m-1) w b) := by
  let en' : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+K-c) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K-c))⟦(1:ℤ)⟧ :=
    by simpa only [Nat.add_sub_cancel_left] using en
  let a' : BiHom m w
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+K-c)) :=
    by simpa only [Nat.add_sub_cancel_left] using a
  let b' : BiHom (m-1) w
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K-c)) :=
    by simpa only [Nat.add_sub_cancel_left] using b
  have transport (n : ℕ) (hn : n=K)
      (hE : (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) K ≅
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K)⟦(1:ℤ)⟧) =
        (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) n ≅
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)⟦(1:ℤ)⟧))
      (hA : BiHom m w (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) K) =
        BiHom m w (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) n))
      (hB : BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K) =
        BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)) :
      (XModLambdaN.incl _ n≫(hE.mp en).hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ n)) ∧
      hA.mp a≫(hE.mp en).hom=ordinarySuspendedRepresentative _ m w (hB.mp b) := by
    subst n
    exact ⟨hen,hab⟩
  have hh : (XModLambdaN.incl _ (c+K-c)≫en'.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+K-c))) ∧
      a'≫en'.hom=ordinarySuspendedRepresentative _ m w b' := by
    exact transport (c+K-c) (by omega) _ _ _
  exact finite_coefficient_shift_ordinary_representative X (c+K) c (by omega) m w
    en' eN hh.1 heN a' b' hh.2

private theorem finite_may_signed_target_ordinary
    (A : SyntheticSpectrum) (N c : ℕ) (hc : 0<c) (hcN : c<N) (m w : ℤ)
    (a : BiHom (m-1) (w+c) (XModLambdaN A (N-c))) :
    (-(biSuspensionHomEquiv m w c (XModLambdaN A (N-c))).symm a ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((model.quotients.tower A).triangle hc hcN).lambdaMap) =
      ordinarySuspendedRepresentative _ m w
        (finiteMayNativeTargetClass A N c hcN m w a) := by
  apply (cancel_mono ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)).mp
  simpa only [ordinarySuspendedRepresentative,Category.assoc,Iso.hom_inv_id_app,
    Category.comp_id] using finite_may_signed_target_eq_suspension A N c hc hcN m w a

private theorem finite_coefficient_insert_weight_detects
    (X : ClassicalObject) (c K : ℕ) (hK : 0<K) (m s t w : ℤ)
    (hm : m=t-s) (hw : 0≤t-w ∧ t-w<(K:ℤ)) (x : Ambient model X (s,t))
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K))
    (ha : Detects (model.convergence (.quotient K (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) K).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) (homotopyRegrade hm rfl a)) :
    Detects (model.convergence (.quotient (c+K) (.nu X))) (s,t,w-c)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+K)).pageMap
        2 (s,t,w-c) (nuWeightLabel model X s t (w-c) (by omega) x))
      (homotopyRegrade hm rfl (finiteCoefficientInsert _ c K hK m w a)) := by
  subst m
  let a' : BiHom (t-s) w
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K-c)) :=
    by simpa only [Nat.add_sub_cancel_left] using a
  have transport (n : ℕ) (hn : n=K)
      (hA : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K) =
        BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)) :
      Detects (model.convergence (.quotient n (.nu X))) (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap
          2 (s,t,w) (nuWeightLabel model X s t w (by omega) x)) (hA.mp a) := by
    subst n
    exact ha
  have ha' : Detects (model.convergence (.quotient (c+K-c) (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+K-c)).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x)) a' :=
    transport (c+K-c) (by omega) _
  exact finite_coefficient_shift_detects X (c+K) c (by omega) s t w (by omega) x a' ha'

private theorem finite_weight_detection_regrade
    (X : ClassicalObject) (N : ℕ) (s t w w' : ℤ) (hw : w≤t) (hw' : w'≤t)
    (hww' : w=w') (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (ha : Detects (model.convergence (.quotient N (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w hw x)) a) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,w')
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w') (nuWeightLabel model X s t w' hw' x))
      (homotopyRegrade rfl hww' a) := by
  subst w'
  exact ha

/-- The same signed May output, extended by c coefficients, has the
prescribed native target label in the last layer c+q. -/
private theorem finite_may_signed_target_at_level
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient model X (s+q+1,t+q))
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (q+1)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ bN : BiHom ((t-s)-1) (t-c)
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu X))) (s+q+1,t+q,t-c)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))).pageMap
          2 (s+q+1,t+q,t-c) (nuWeightLabel model X (s+q+1) (t+q) (t-c) (by omega) v))
        (homotopyRegrade (by dsimp; omega) rfl bN) ∧
      finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
      ordinarySuspendedRepresentative _ (t-s) (t-c) bN := by
  dsimp only
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let α : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) :=
    homotopyRegrade (by omega) rfl (nativeFirstLabel X (s+q+1) (t+q) v)
  let α' : BiHom ((t-s)-1) (t+q) (XModLambdaN A (q+1-q)) :=
    by simpa only [Nat.add_sub_cancel_left] using α
  let b₀ := finiteMayNativeTargetClass A (q+1) q (by omega) (t-s) t α'
  let bN := finiteCoefficientInsert A c (q+1) (by omega) ((t-s)-1) t b₀
  refine ⟨bN,?_,?_⟩
  · have hα := first_label_detects_unshifted X 1 (by omega) (s+q+1) (t+q) v
      (nativeFirstLabel X (s+q+1) (t+q) v) (by
        rw [(model.quotients.tower _).rho_id,Category.comp_id]
        rfl)
    have hα' : Detects (model.convergence (.quotient (q+1-q) (.nu X)))
        (s+q+1,t+q,t+q)
        (regradeE2 (by simp) (finiteTargetLabel model X (q+1-q) (s+q+1) (t+q) 0 v))
        (homotopyRegrade (by dsimp; omega) rfl α') := by
      have transport (n : ℕ) (hn : n=1)
          (hA : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) =
            BiHom ((t-s)-1) (t+q) (XModLambdaN A n)) :
          Detects (model.convergence (.quotient n (.nu X))) (s+q+1,t+q,t+q)
            (regradeE2 (by simp) (finiteTargetLabel model X n (s+q+1) (t+q) 0 v))
            (homotopyRegrade (by dsimp; omega) rfl (hA.mp α)) := by
        subst n
        convert hα using 1
        change homotopyRegrade (show ((t-s)-1)=(t+q)-(s+q+1) by omega) rfl
          (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+q+1) (t+q) v)) = _
        rw [output_regrade_trans]
        rfl
      exact transport (q+1-q) (by omega) _
    have hd := finite_may_native_target_detects X (q+1) q (by omega) (t-s) t
      (s+q+1) (t+q) (by omega) rfl v α' hα'
    rw [←finite_coefficient_weight_label] at hd
    have hd' := finite_weight_detection_regrade X (q+1) (s+q+1) (t+q)
      ((t+q)-q) t (by omega) (by omega) (by omega) v _ hd
    have hbase : Detects (model.convergence (.quotient (q+1) (.nu X)))
        (s+q+1,t+q,t)
        ((model.family.quotientProjection A (q+1)).pageMap 2 (s+q+1,t+q,t)
          (nuWeightLabel model X (s+q+1) (t+q) t (by omega) v))
        (homotopyRegrade (by dsimp; omega) rfl b₀) := by
      simpa only [b₀,A,SyntheticObject.obj,output_regrade_trans] using hd'
    exact finite_coefficient_insert_weight_detects X c (q+1) (by omega)
      ((t-s)-1) (s+q+1) (t+q) t (by omega) (by omega) v b₀ hbase
  · have hbase := finite_may_signed_target_ordinary A (q+1) q hq (by omega) (t-s) t α'
    have hbase' :
        (-((biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (by simpa only [show q.succ-q=1 by omega] using
              ((model.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap)) =
        ordinarySuspendedRepresentative _ (t-s) t b₀ := by
      have transport (n : ℕ) (hn : n=1)
          (hA : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) =
            BiHom ((t-s)-1) (t+q) (XModLambdaN A n))
          (ln : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n) ⟶
            XModLambdaN A (q+1))
          (hL : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n) ⟶
            XModLambdaN A (q+1)) =
            ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1) ⟶
            XModLambdaN A (q+1))) :
          (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A n)).symm (hA.mp α) ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map ln) =
          (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map (hL.mp ln)) := by
        subst n
        rfl
      have hraw :
          (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A (q+1-q))).symm α' ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map
              ((model.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap) =
          (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map
              (by simpa only [show q.succ-q=1 by omega] using
                ((model.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap)) :=
        transport (q+1-q) (by omega) _ _ _
      exact hraw.symm.trans hbase
    apply finite_coefficient_insert_ordinary_representative X c (q+1) (by omega)
      (t-s) t en eN hen heN _ b₀
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Preadditive.neg_comp,α] using hbase'

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
