module

import all KIP126.ProofTools.FiniteLifting.ClassicalLift
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem native_bottom_source_exists
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ permanentCycles model X (s,t)) :
    ∃ a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      Detects (model.convergence (.nu X)) (s,t,t)
        (nuWeightLabel model X s t t (by omega) x) a ∧
      a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let z := (KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (permanentCycles model X (s,t))
      (boundaries model X (1+t-t) (s,t)) ⟨x,hx⟩)
  have hz : HasInfinityRepresentative _ 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) z := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x z).mpr
    exact ⟨hx,AddEquiv.apply_symm_apply _ _⟩
  let F := model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))
  haveI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((model.convergence (.nu X)).identification (s,t,t)).hom z)
  let a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)) :=
    (F.F s (t-s,t)).arrow ar
  have ha : Detects (model.convergence (.nu X)) (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) a := ⟨z,hz,ar,rfl,har.symm⟩
  have hq := detects_map (.nu X) (.quotient 1 (.nu X))
    (XModLambdaN.incl _ 1) (s,t,t) _ _ ha
  have hf := finite_detected_bottom_first X 1 (by decide) s t x _ hq
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hf
  exact ⟨a,ha,hf⟩

private theorem lambda_multiply_raw {A : SyntheticSpectrum} (m w : ℤ)
    (k : ℕ) (a : BiHom m w A) :
    lambdaMultiply k a = homotopyRegrade (by dsimp; omega) (by dsimp; omega)
      (shiftHomotopyClass (0,-(k:ℤ)) (m,w) a ≫ lambdaPow k A) := by
  simp only [lambdaMultiply,shiftHomotopyClass,regrade_precomp,Category.assoc,
    lambdaPow_naturality]
  rfl

private theorem lambda_multiply_zero {A : SyntheticSpectrum} (m w : ℤ)
    (a : BiHom m w A) :
    homotopyRegrade rfl (show w-(0:ℕ)=w by simp) (lambdaMultiply 0 a) = a := by
  rw [lambda_multiply_raw,normalized_homotopy_regrade_trans,regrade_comp]
  exact shift_zero_lambda A (m,w) a

private theorem shifted_native_bottom_detects
    (X : ClassicalObject) (e s t : ℤ) (he : e=0 ∨ e=1)
    (x : Ambient model X (s,t)) (hx : x ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) a) :
    Detects (model.convergence (.shift (0,e) (.nu X))) (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x))
      (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,e) (t-s,t) a)) := by
  let p : ℤ×ℤ := (t-s,t)
  let δ : ℤ×ℤ := (0,e)
  have hi : (s,t,t)=(s,p.1+s,p.2) := by simp [p]
  have hiS : (s,t,t+e-(0:ℕ))=(s,(p+δ).1+s,(p+δ).2) := by
    ext <;> dsimp [p,δ] <;> omega
  have ha' := detects_transport hi _ _ ha
  have ha'' : Detects (model.convergence (.nu X)) (s,p.1+s,p.2)
      (regradeE2 hi (nuWeightLabel model X s t t (by omega) x))
      (homotopyRegrade (by dsimp [p]; omega) rfl a) := by convert ha' using 1
  have hs := detects_shift (.nu X) δ p s _ a ha''
  obtain ⟨z,hz,_,_,_⟩ := ha
  obtain ⟨zN,hzN⟩ := shifted_full_source_exists X e s t x hx
  have hzN' := representative_transport hiS _ _ hzN
  have hz' := representative_transport hi _ _ hz
  have hzshift := ((KIP126.AdamsSynthetic.Standard.essShift δ).representative_iff
    (.nu X) 2 (by decide) p s _ _).mp hz'
  have heq := normalized_source_infinity_shift X e s t he x z hz _ hzN'
  obtain ⟨zs,hzs,br,hbr,hgbr⟩ := hs
  have hzs' := hzs.unique hzshift
  have hN : HasInfinityRepresentative _ 2 (s,(p+δ).1+s,(p+δ).2)
      (regradeE2 hiS (model.comparison.nuE2 X e s t 0 x)) zs := by
    have hh := hzs'.trans heq
    exact hh.symm ▸ hzN'
  have hsN : Detects (model.convergence (.shift δ (.nu X)))
      (s,(p+δ).1+s,(p+δ).2)
      (regradeE2 hiS (model.comparison.nuE2 X e s t 0 x))
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a)) :=
    ⟨zs,hN,br,hbr,hgbr⟩
  have hj : (s,(p+δ).1+s,(p+δ).2)=(s,t,t+e) := by
    ext <;> dsimp [p,δ] <;> omega
  have hout := detects_transport hj _ _ hsN
  convert hout using 1
  · simp only [normalized_regrade_trans]
  · simp only [normalized_homotopy_regrade_trans]
    rfl

private theorem native_lambda_source_detects
    (X : ClassicalObject) (k : ℕ) (s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.nu X)) (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) x) (lambdaMultiply k a) := by
  by_cases hk : 0 < k
  · exact nu_lambda_detects X k hk s t x hx a ha
  · have hk0 : k=0 := by omega
    subst k
    have hd := nu_first_label_detects X s t x hx a ha
    have hi : (s,t,t)=(s,t,t-(0:ℕ)) := by simp
    have ht := detects_transport hi _ _ hd
    have hl : HEq (lambdaMultiply 0 a) a :=
      (homotopyRegrade_heq rfl (show t-(0:ℕ)=t by simp) (lambdaMultiply 0 a)).symm.trans
        (heq_of_eq (lambda_multiply_zero (t-s) t a))
    convert ht using 1
    · exact eq_of_heq ((nuWeight_label_heq X s t (t-(0:ℕ)) s t t
        rfl rfl (by simp) (by omega) (by omega) x x (HEq.rfl)).trans
        (regradeE2_heq hi _).symm)
    · exact eq_of_heq (hl.trans (homotopyRegrade_heq _ _ a).symm)

private theorem realization_lambda_multiply
    (R : RealizationCoordinates model) {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A) :
    (R.sphere m (w-k)).hom ≫ model.recovery.realization.map (lambdaMultiply k a) =
      (R.sphere m w).hom ≫ model.recovery.realization.map a := by
  have hl : lambdaMultiply k a = lambdaMultiply k (𝟙 (Smn m w)) ≫ a := by
    simp only [lambdaMultiply,Category.comp_id,Category.assoc]
  rw [hl,Functor.map_comp,←Category.assoc,R.lambda]

private theorem lambda_multiply_shift {A : SyntheticSpectrum}
    (m w e : ℤ) (k : ℕ) (a : BiHom m w A) :
    homotopyRegrade (m' := m) (w' := w+e-k) (by simp) (by dsimp; omega)
      (shiftHomotopyClass (0,e) (m,w-k) (lambdaMultiply k a)) =
      lambdaMultiply k
        (homotopyRegrade (m' := m) (by simp) rfl
          (shiftHomotopyClass (0,e) (m,w) a)) := by
  have h := congrArg (homotopyRegrade
    (show (((m,w)+(0,-(k:ℤ)))+(0,e)).1=m by dsimp; omega)
    (show (((m,w)+(0,-(k:ℤ)))+(0,e)).2=w+e-k by dsimp; omega))
    (lambda_raw_shift_comm (0,e) (m,w) k A a)
  have shift_input_regrade {m₀ m₁ w₀ w₁ : ℤ}
      (hm : m₀=m₁) (hw : w₀=w₁) (a₀ : BiHom m₀ w₀ A) :
      shiftHomotopyClass (0,e) (m₁,w₁) (homotopyRegrade hm hw a₀) =
        homotopyRegrade (congrArg (fun z : ℤ => z+0) hm)
          (congrArg (fun z : ℤ => z+e) hw)
          (shiftHomotopyClass (0,e) (m₀,w₀) a₀) := by
    subst m₁
    subst w₁
    rfl
  rw [lambda_regrade,lambda_multiply_raw m w k a]
  conv_rhs => rw [lambda_multiply_raw]
  rw [shift_input_regrade]
  simpa only [normalized_homotopy_regrade_trans,Prod.eta] using h

private theorem shifted_full_source_projection
    (X : ClassicalObject) (q k : ℕ) (e s t : ℤ)
    (a : BiHom (t-s) (t-k) (model.nu.functor.obj (X.obj model.auxiliary))) :
    finiteLevelNormalizedRepresentative X e q k s t (a ≫ XModLambdaN.incl _ q) =
      homotopyRegrade (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,e) (t-s,t-k) a) ≫ XModLambdaN.incl _ q := by
  apply (cancel_mono (levelQuotientShiftIso X e q).hom).mp
  simp only [finiteLevelNormalizedRepresentative,Category.assoc,Iso.inv_hom_id,
    Category.comp_id,level_quotient_shift_incl]
  simp only [shiftHomotopyClass,Functor.map_comp,regrade_precomp,Category.assoc]

/-- A permanent classical source has an actual full representative whose
finite projection has the intrinsic level label and whose realization is
detected by the original classical source. Only zero-level normalized-label
calibration is used; lambda multiplication preserves the realization. -/
private theorem level_full_source_with_realization
    (R : RealizationCoordinates model) (hcomp : LambdaInversionAdamsComparison model R)
    (X : ClassicalObject) (q k e : ℕ) (he : e=0 ∨ e=1) (s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x ∈ permanentCycles model X (s,t)) :
    ∃ a : BiHom (t-s) (t+(e:ℤ)-k)
      ((SyntheticObject.shift (0,(e:ℤ)) (.nu X)).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient q (.shift (0,(e:ℤ)) (.nu X))))
        (s,(t-s)+s,t+(e:ℤ)-k)
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel X q e s t k x)
        (homotopyRegrade (by dsimp; omega) rfl (a ≫ XModLambdaN.incl _ q)) ∧
      ClassicalDetects (model.classicalConvergence X) (s,t) x
        ((R.sphere (t-s) (t+(e:ℤ)-k)).hom ≫ model.recovery.realization.map a ≫
          (hcomp.shiftedNu X e).target.hom) := by
  obtain ⟨b,hb,hbfirst⟩ := native_bottom_source_exists X s t x hx
  let a0 : BiHom (t-s) (t+(e:ℤ))
      ((SyntheticObject.shift (0,(e:ℤ)) (.nu X)).obj model.nu model.auxiliary) :=
    homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,(e:ℤ)) (t-s,t) b)
  let a := lambdaMultiply k a0
  have hn := native_lambda_source_detects X k s t x hx b hbfirst
  have hnq := detects_map (.nu X) (.quotient q (.nu X))
    (XModLambdaN.incl _ q) (s,t,t-k) _ _ hn
  have hlabel : nuWeightLabel model X s t (t-k) (by omega) x =
      targetNuLabel model X s t k x := by
    unfold nuWeightLabel
    have hk : (t-(t-k)).toNat=k := by omega
    have transport (j : ℕ) (hj : j=k) (hi : (s,t,t-j)=(s,t,t-k)) :
        regradeE2 hi (targetNuLabel model X s t j x) = targetNuLabel model X s t k x := by
      subst j
      rfl
    exact transport _ hk _
  rw [hlabel] at hnq
  have hnq' : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (lambdaMultiply k b ≫ XModLambdaN.incl _ q) := hnq
  have hs := finite_level_normalized_representative_detects X e q k s t x _ hnq'
  rw [shifted_full_source_projection,lambda_multiply_shift] at hs
  refine ⟨a,hs,?_⟩
  have he' : (e:ℤ)=0 ∨ (e:ℤ)=1 := by rcases he with rfl|rfl <;> simp
  have ha0 := shifted_native_bottom_detects X e s t he' x hx b hb
  have hc := (hcomp.shiftedNu X e).detects s t (t+(e:ℤ)) _ a0 ha0
  have he2 : (hcomp.shiftedNu X e).e2Map (t+(e:ℤ)) (s,t)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) = x := by
    rw [KIP126.ProofTools.Paper.paper_e2Map_regrade model (hcomp.shiftedNu X e)
      s t (t+(e:ℤ)-(0:ℕ)) (t+(e:ℤ)) (by simp)]
    exact hcomp.shiftedNu_e2 X e s t 0 x
  rw [he2] at hc
  change ClassicalDetects _ _ x
    ((R.sphere (t-s) (t+(e:ℤ)-k)).hom ≫
      model.recovery.realization.map (lambdaMultiply k a0) ≫ (hcomp.shiftedNu X e).target.hom)
  rw [←Category.assoc,realization_lambda_multiply]
  simpa only [Category.assoc] using hc


end
end KIP126.ProofTools.Internal.FiniteLifting
