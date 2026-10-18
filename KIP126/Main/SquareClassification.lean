module

public import KIP126.Main.Conditions

import all KIP126.Main.RepresentativeResults
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.AlphaOne.Coherence

/-! The stem-124 square classification. The finite-page analysis is the
proved Selected/ThetaData argument at bbac1fc05843 (MIT). Its detected
branches admit exact representatives: divide the next-filtration error by
one additional lambda, and absorb that error into the chosen lift. -/
@[expose] section
namespace KIP126.Main
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Computation.Standard (U correction)
open KIP126.Main.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem square_regrade_comp {m m' w w' : ℤ}
    {X Y : SyntheticSpectrum} (hm : m=m') (hw : w=w')
    (a : BiHom m w X) (f : X ⟶ Y) :
    homotopyRegrade hm hw (a ≫ f)=(homotopyRegrade hm hw a) ≫ f := by
  subst m'
  subst w'
  rfl

private theorem square_lambda_comp {m w : ℤ} {X Y : SyntheticSpectrum}
    (k : ℕ) (a : BiHom m w X) (f : X ⟶ Y) :
    lambdaMultiply k (a ≫ f)=lambdaMultiply k a ≫ f := by
  simp only [lambdaMultiply,Category.assoc]

private theorem square_lambda_add {m w : ℤ} {X : SyntheticSpectrum}
    (k : ℕ) (a b : BiHom m w X) :
    lambdaMultiply k (a+b)=lambdaMultiply k a+lambdaMultiply k b := by
  simp only [lambdaMultiply,Preadditive.comp_add]

private theorem square_add_correction {m w : ℤ}
    (a b : BiHom m w (S_0_0 : SyntheticSpectrum)) : a=b+(a-b) := by
  abel

private theorem sphere_filtration_lambda (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    FiltrationAtLeast model.syntheticTower s a ↔
      ∃ b : BiHom m (m+s) (S_0_0 : SyntheticSpectrum),
        homotopyRegrade rfl (by rw [Int.toNat_of_nonneg (by omega)]; omega)
          (lambdaMultiply (m+s-w).toNat b)=a := by
  have hnu := KIP126.Literature.Standard.selected_filtration_lambda .sphere m w s h
    (a ≫ model.nu.unitIso.inv)
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := hnu.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha)
    refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
    simpa only [square_lambda_comp,square_regrade_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z => z ≫ model.nu.unitIso.hom) hb
  · rintro ⟨b,hb⟩
    have hn := hnu.mpr ⟨b ≫ model.nu.unitIso.inv,by
      simpa only [square_lambda_comp,square_regrade_comp,Category.assoc] using
        congrArg (fun z => z ≫ model.nu.unitIso.inv) hb⟩
    have hh := map_filtration (.nu .sphere) .sphere model.nu.unitIso.hom
      (a ≫ model.nu.unitIso.inv) hn
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hh

private theorem square_lambda_six_one
    (c : BiHom 124 135 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (124,135) (0,-1) (0,-6)
    (124,134) (0,-7) (124,128) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,135) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 124 135)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 1 6 7 (by decide) (Smn 124 135)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem square_lambda_nine_one
    (c : BiHom 124 138 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 9 (lambdaMultiply 1 c) = lambdaMultiply 10 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (124,138) (0,-1) (0,-9)
    (124,137) (0,-10) (124,128) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 9
    ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 9 (lambdaPow 1 (Smn 124 138)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 1 9 10 (by decide) (Smn 124 138)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem square_lambda_zero_124_137 (a : BiHom 124 137 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (124,137) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 124 137 : SyntheticSpectrum) := by
    change (biShiftAddIso (124,137) (0,0) (124,137) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (124,137) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

private theorem correction_choice_exists :
    ∃ c : BiHom 124 137 (S_0_0 : SyntheticSpectrum),
      DetectsNonzero (model.convergence .sphere) (13,137,137)
        (model.comparison.sphereE2 13 137 0 correction) c ∧
      KIP126.Literature.sphereFirstQuotient model 13 137 (quotientClass 1 c)=correction := by
  obtain ⟨z,hz,hzn,_⟩ := correction_infinity_generated
  have hp : IsPermanentCycle model.classical.sphere (13,137) correction := ⟨z,hz⟩
  have hne : correction≠0 := by
    intro h0
    let P := model.classical.sphere.ssData (13,137)
    have hh := P.infinity_projection_eq_of_page_projection_eq ↑(2-model.classical.sphere.r₀).toNat z 0
      (by simpa only [map_zero] using hz.trans h0)
    exact hzn (by simpa only [map_zero] using hh)
  obtain ⟨c,hc⟩ := sphere_permanent_first_quotient_lift 13 137 correction hp
  refine ⟨c,?_,hc⟩
  have hd := model.sphereDetectionCompatible.homotopy_lambda 13 137 0 c
  have hcl := hc
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hcl
  rw [square_lambda_zero_124_137,hcl] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩ := hd
  refine ⟨e,he,?_⟩
  let f := XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1
  have hf := KIP126.ProofTools.Operations.family_infinity_representative_map f (13,137,137-0) _ _ he
  have hfn := finite_sphere_infinity_nonzero 1 (by decide) 13 137 correction hne _ hf
  intro he0
  apply hfn
  rw [he0,map_zero]

private theorem theta5_square_nonzero_detection_exact_representative
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (hc4 : Theta5SquareNonzeroDetectionAt theta) :
    ∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u ∧
      sphereProduct theta theta=lambdaMultiply 6 u := by
  obtain ⟨u0,hu0⟩ := KIP126.Main.u_choice_exists
  have hl := sphere_zero_weight_label_10_134 U u0 hu0.1
  have hd := model.sphereDetectionCompatible.homotopy_lambda 10 134 6 u0
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hl
  rw [hl] at hd
  have hdelta := detects_sub_filtration (model.convergence .sphere) (10,134,128) hc4.1 hd
  have hdiv := sphere_filtration_lambda 124 128 11 (by decide)
    ((show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from sphereProduct theta theta)-(show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 u0))
  change FiltrationAtLeast model.syntheticTower 11 _ ↔
    ∃ b : BiHom 124 135 (S_0_0 : SyntheticSpectrum),
      lambdaMultiply 7 b=(show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from sphereProduct theta theta)-(show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 u0) at hdiv
  obtain ⟨b,hb⟩ := hdiv.mp hdelta
  let u : BiHom 124 134 (S_0_0 : SyntheticSpectrum) := u0+(show BiHom 124 134 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 b)
  have herror : FiltrationAtLeast model.syntheticTower 11 (show BiHom 124 134 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 b) := by
    have h := sphere_filtration_lambda 124 134 11 (by decide) (lambdaMultiply 1 b)
    exact h.mpr ⟨b,rfl⟩
  have hu : UChoice u := by
    refine ⟨Choice.detects_of_difference_in_next_filtration (model.convergence .sphere)
      (10,134,134) hu0.1 ?_,hu0.2⟩
    change FiltrationAtLeast model.syntheticTower 11 (u-u0)
    simpa only [u,add_sub_cancel_left] using herror
  refine ⟨u,hu,?_⟩
  have he : lambdaMultiply 6 u=
      (show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 u0)+
      (show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 7 b) := by
    dsimp only [u]
    rw [square_lambda_add,square_lambda_six_one]
  rw [he,hb]
  exact square_add_correction (m := 124) (w := 128) _ _

private theorem correction_exact_representative
    (a : BiHom 124 128 (S_0_0 : SyntheticSpectrum))
    (ha : DetectsNonzero (model.convergence .sphere) (13,137,128)
      (model.comparison.sphereE2 13 137 9 correction) a) :
    ∃ c : BiHom 124 137 (S_0_0 : SyntheticSpectrum),
      DetectsNonzero (model.convergence .sphere) (13,137,137)
        (model.comparison.sphereE2 13 137 0 correction) c ∧ a=lambdaMultiply 9 c := by
  obtain ⟨c0,hc0,hl⟩ := correction_choice_exists
  have hd := model.sphereDetectionCompatible.homotopy_lambda 13 137 9 c0
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hl
  rw [hl] at hd
  have hdelta := detects_sub_filtration (model.convergence .sphere) (13,137,128) ha.1 hd
  have hdiv := sphere_filtration_lambda 124 128 14 (by decide) (a-(show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 9 c0))
  change FiltrationAtLeast model.syntheticTower 14 _ ↔
    ∃ b : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 10 b=a-(show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 9 c0) at hdiv
  obtain ⟨b,hb⟩ := hdiv.mp hdelta
  let c : BiHom 124 137 (S_0_0 : SyntheticSpectrum) := c0+(show BiHom 124 137 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 b)
  have herror : FiltrationAtLeast model.syntheticTower 14 (show BiHom 124 137 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 b) := by
    have h := sphere_filtration_lambda 124 137 14 (by decide) (lambdaMultiply 1 b)
    exact h.mpr ⟨b,rfl⟩
  have hc : DetectsNonzero (model.convergence .sphere) (13,137,137)
      (model.comparison.sphereE2 13 137 0 correction) c := by
    refine ⟨Choice.detects_of_difference_in_next_filtration (model.convergence .sphere)
      (13,137,137) hc0.1 ?_,hc0.2⟩
    change FiltrationAtLeast model.syntheticTower 14 (c-c0)
    simpa only [c,add_sub_cancel_left] using herror
  refine ⟨c,hc,?_⟩
  have he : lambdaMultiply 9 c=
      (show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 9 c0)+
      (show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 10 b) := by
    dsimp only [c]
    rw [square_lambda_add,square_lambda_nine_one]
  rw [he,hb]
  exact square_add_correction (m := 124) (w := 128) _ _

/-- Detection form of the stem-124 classification, from the proved finite-page
analysis. It holds for every element in the theta degree. -/
private theorem theta_square_detection_cases
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    Theta5SquareNonzeroDetectionAt theta ∨
      DetectsNonzero (model.convergence .sphere) (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) (sphereProduct theta theta) ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum),
        lambdaMultiply 10 a=sphereProduct theta theta :=
  Internal.Selected.theta_three_cases theta

/-- Exact lambda-multiple representatives for the three detection branches.
The first retains UChoice, and the second retains the correction detector. -/
public theorem theta_square_three_possibilities
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    (∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u ∧
      sphereProduct theta theta=lambdaMultiply 6 u) ∨
    (∃ c : BiHom 124 137 (S_0_0 : SyntheticSpectrum),
      DetectsNonzero (model.convergence .sphere) (13,137,137)
        (model.comparison.sphereE2 13 137 0 correction) c ∧
      sphereProduct theta theta=lambdaMultiply 9 c) ∨
    (∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum),
      sphereProduct theta theta=lambdaMultiply 10 a) := by
  rcases theta_square_detection_cases theta with hfirst|hsecond|hthird
  · exact Or.inl (theta5_square_nonzero_detection_exact_representative theta hfirst)
  · exact Or.inr (Or.inl (correction_exact_representative _ hsecond))
  · exact Or.inr (Or.inr (by obtain ⟨a,ha⟩ := hthird; exact ⟨a,ha.symm⟩))

end
end KIP126.Main
