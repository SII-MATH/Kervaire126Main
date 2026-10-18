module
import all KIP126.Main.SectionSeven.AnyYFinite
import all KIP126.Main.SectionSeven.AnyYError
import all KIP126.Main.SectionSeven.WeakStrip
import all KIP126.Main.SectionSeven.WeakStripTorsion
/-! Torsion-preserving filtration peeling and seventh-error vanishing,
AnyYHelpers:1595–1664,2831–2842 at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem anyy_af15_source_boundary : cycles model .sphere 8 (15,140) ≤ boundaries model .sphere 4 (15,140) := by
  intro x hx
  have hx' : Normalized.label (15,140) x ∈ NuError.nCycles 8 (15,140) := by
    change NuError.denormalize (15,140) (Normalized.label (15,140) x) ∈ cycles model .sphere 8 (15,140)
    rw [NuError.denormalize_label]; exact hx
  have h := AnyYFinite.y_detection_page_af15_source_boundary hx'
  change NuError.denormalize (15,140) (Normalized.label (15,140) x) ∈ boundaries model .sphere 4 (15,140) at h
  rwa [NuError.denormalize_label] at h

theorem anyy_af16_source_boundary : cycles model .sphere 7 (16,141) ≤ boundaries model .sphere 4 (16,141) := by
  intro x hx
  have hx' : Normalized.label (16,141) x ∈ NuError.nCycles 7 (16,141) := by
    change NuError.denormalize (16,141) (Normalized.label (16,141) x) ∈ cycles model .sphere 7 (16,141)
    rw [NuError.denormalize_label]; exact hx
  have h := AnyYFinite.y_detection_page_af16_source_boundary hx'
  change NuError.denormalize (16,141) (Normalized.label (16,141) x) ∈ boundaries model .sphere 4 (16,141) at h
  rwa [NuError.denormalize_label] at h

theorem lambda_multiply_zero_precomp {A : SyntheticSpectrum} {m w m' w' : ℤ}
    (b : ℕ) (f : Smn (Syn:=SyntheticSpectrum) m' w' ⟶ Smn m w) (x : BiHom m w A)
    (hx : lambdaMultiply b x=0) : lambdaMultiply b (f≫x)=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at hx ⊢
  rw [←Category.assoc,←lambdaPow_naturality b f,Category.assoc,hx,Limits.comp_zero]

theorem lambda_multiply_zero_iterated {A : SyntheticSpectrum} {m w : ℤ}
    (a b : ℕ) (x : BiHom m w A) (hx : lambdaMultiply b x=0) :
    lambdaMultiply b (lambdaMultiply a x)=0 := by
  let f : Smn (Syn:=SyntheticSpectrum) m (w-a) ⟶ Smn m w :=
    eqToHom (by congr 1; simp) ≫
      (SyntheticCategory.biShift_comp (m,w) (0,-(a:ℤ))).inv.app S_0_0 ≫ lambdaPow a (Smn m w)
  have he : lambdaMultiply a x=f≫x := by simp only [f,lambdaMultiply,Category.assoc]
  rw [he]
  exact lambda_multiply_zero_precomp b f x hx

theorem anyy_boundary_filtration_peel
    (s t : ℤ) (k : ℕ) (hk : k<9)
    (hb : cycles model .sphere (9-k) (s,t) ≤ boundaries model .sphere 4 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    ∃ a' : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiltrationAtLeast model.syntheticTower (s+1) a' ∧
      lambdaMultiply 6 a'=lambdaMultiply 6 a := by
  obtain ⟨x,hxc,hxa⟩ := finite_sphere_filtration_has_cycle_label 9 k (by decide) hk s t a ha
  obtain ⟨b,hbq,hbt⟩ := sphere_boundary_submodule_torsion_lift s t 4 (by decide) x (hb hxc)
  let a0 : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := quotientClass 9 (lambdaMultiply k b)
  have ha0 : Detects (model.convergence (.quotient 9 .sphere)) (s,t,t-k) (quotientLabel 9 s t k x) a0 := by
    have h := model.sphereDetectionCompatible.homotopy_lambda s t k b
    change Detects (model.convergence .sphere) (s,t,t-k)
      (sphereLabel s t k (KIP126.Literature.sphereFirstQuotient model s t (quotientClass 1 b))) (lambdaMultiply k b) at h
    rw [hbq] at h
    exact detects_map .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9) (s,t,t-k) _ _ h
  have ha0zero : lambdaMultiply 6 a0=0 := by
    have hb6 := lambda_multiply_zero_mono 3 6 (by decide) b hbt
    have hb6k := lambda_multiply_zero_iterated k 6 b hb6
    simpa only [a0,quotientClass,lambdaMultiply,Category.assoc,Limits.zero_comp] using
      congrArg (fun f=>f≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 9) hb6k
  refine ⟨a-a0,detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (s,t,t-k) hxa ha0,?_⟩
  have hdist : lambdaMultiply 6 (a-a0)=lambdaMultiply 6 a-lambdaMultiply 6 a0 := by
    simp only [lambdaMultiply,Preadditive.comp_sub]
  rw [hdist,ha0zero,sub_zero]

theorem anyy_lambda_six_filtration_fifteen_zero
    (a : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 15 a) : lambdaMultiply 6 a=0 := by
  obtain ⟨b,hb,hab⟩ := anyy_boundary_filtration_peel 15 140 1 (by decide) anyy_af15_source_boundary a ha
  obtain ⟨c,hc,hbc⟩ := anyy_boundary_filtration_peel 16 141 2 (by decide) anyy_af16_source_boundary b hb
  have hc17 := lambda_filtration_preserved 6 17 c hc
  have hz := sphere_quotient_high_filtration_zero 9 (by decide) 125 133 17 (by decide)
    (lambdaMultiply 6 c) hc17
  exact hab.symm.trans (hbc.symm.trans hz)

theorem anyy_seventh_error_zero (a : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    lambdaMultiply 7 a=0 := by
  have hf := finite_sphere_bottom_filtration 9 (by decide) 15 140 a
  have hf' := lambda_filtration_preserved 1 15 a hf
  have hz := anyy_lambda_six_filtration_fifteen_zero (lambdaMultiply 1 a) hf'
  rw [y_detection_toda_main_lambda_six_one] at hz
  exact hz
end
end KIP126.Main.SectionSeven.Internal
