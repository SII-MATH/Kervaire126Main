module
public import KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! The existing λ-associativity and target lifting proof, retained from
NuTargetHelpers.lean:1118–1232,1261–1326 at bbac1fc05843 (MIT). -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal
noncomputable section
def shiftSwap (a b : ℤ × ℤ) (A : SyntheticSpectrum) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
    (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
  (biShiftAddIso a b (a+b) rfl).app A ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
theorem lambda_one_shift (coh : BiShiftCoherence SyntheticSpectrum) (a : ℤ×ℤ) (A : SyntheticSpectrum) :
    lambdaPow 1 ((SyntheticCategory.biShift a).obj A)=
      (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
  rw [lambdaPow_one coh,lambdaPow_one coh]
  simpa only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc] using coh.lambda_comm a A
theorem nu_target_lambda_left
    (etaShuffle : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (a : BiHom 122 132 (S_0_0 : SyntheticSpectrum)) :
    sphereAction (lambdaMultiply 1 etaShuffle) a = lambdaMultiply 1 (sphereAction etaShuffle a) := by
  let S := (S_0_0 : SyntheticSpectrum)
  have h₁ := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (3,4) (122,132) (0,-1)
    (125,136) (122,131) (125,135) (by decide) (by decide) (by decide) (by decide) S
  have h₂ := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (3,4) (0,-1) (122,132)
    (3,3) (122,131) (125,135) (by decide) (by decide) (by decide) (by decide) S
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at h₁ h₂
  have hp :
    (SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S ≫
      lambdaPow 1 (Smn 125 136) ≫
      (SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app S =
    (SyntheticCategory.biShift_comp (3,3) (122,132)).inv.app S ≫
      (SyntheticCategory.biShift (122,132)).map
        ((SyntheticCategory.biShift_comp (3,4) (0,-1)).inv.app S) ≫
      (SyntheticCategory.biShift (122,132)).map (lambdaPow 1 (Smn 3 4)) := by
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S ≫
      (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app S) ≫
      lambdaPow 1 ((SyntheticCategory.biShift (122,132)).obj (Smn 3 4)) = _
    rw [lambda_one_shift graded_coherence (122,132) (Smn 3 4)]
    dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
    simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
      Category.comp_id,Category.id_comp]
    simp only [Category.assoc]
    erw [←Category.assoc ((SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S)]
    erw [h₁]
    simp only [Category.assoc,Smn,S,Int.natCast_one,Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (122,132)).map (lambdaPow 1 (Smn 3 4))) h₂.symm)
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
  simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
    (congrArg (fun z => z ≫ (SyntheticCategory.biShift (122,132)).map etaShuffle ≫ a) hp).symm
theorem nu_target_four_one  {X : SyntheticSpectrum} (c : BiHom 125 136 X) :
    lambdaMultiply 4 (lambdaMultiply 1 c)=lambdaMultiply 5 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (125,136) (0,-1) (0,-4)
    (125,135) (0,-5) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 4 ((SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 4 (lambdaPow 1 (Smn 125 136)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add graded_coherence 1 4 5 (by decide) (Smn 125 136)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
  rfl
theorem nu_target_five_one  {X : SyntheticSpectrum} (c : BiHom 122 133 X) :
    lambdaMultiply 5 (lambdaMultiply 1 c)=lambdaMultiply 6 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (122,133) (0,-1) (0,-5)
    (122,132) (0,-6) (122,127) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 5 ((SyntheticCategory.biShift_comp (122,133) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 5 (lambdaPow 1 (Smn 122 133)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add graded_coherence 1 5 6 (by decide) (Smn 122 133)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
  rfl
theorem nu_target_five_two  {X : SyntheticSpectrum} (c : BiHom 122 134 X) :
    lambdaMultiply 5 (lambdaMultiply 2 c)=lambdaMultiply 7 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (122,134) (0,-2) (0,-5)
    (122,132) (0,-7) (122,127) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 5 ((SyntheticCategory.biShift_comp (122,134) (0,-2)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [←reassoc_of% (lambdaPow_naturality 5 (lambdaPow 2 (Smn 122 134)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add graded_coherence 2 5 7 (by decide) (Smn 122 134)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
  rfl
theorem nu_target_lambda_right_five
    (etaAux : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (c : BiHom 122 132 (S_0_0 : SyntheticSpectrum)) :
    sphereAction etaAux (lambdaMultiply 5 c) = lambdaMultiply 5 (sphereAction etaAux c) := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (3,4) (122,132) (0,-5)
    (125,136) (122,127) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 5
    ((SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 5
    ((SyntheticCategory.biShift (122,132)).map etaAux))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (122,132) (0,-5)).inv.naturality etaAux)]
  rfl
theorem nu_target_lambda_four_product
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) (a : BiHom 122 132 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 4 (sphereProduct (lambdaMultiply 1 nu) a)=
      sphereProduct nu (lambdaMultiply 5 a) := by
  change lambdaMultiply 4 (sphereAction (lambdaMultiply 1 nu) a)=sphereAction nu (lambdaMultiply 5 a)
  rw [nu_target_lambda_left,nu_target_four_one,nu_target_lambda_right_five]
theorem lambda_four_one
    (c : BiHom 125 140 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 4 (lambdaMultiply 1 c) = lambdaMultiply 5 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (125,140) (0,-1) (0,-4)
    (125,139) (0,-5) (125,135) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 4
    ((SyntheticCategory.biShift_comp (125,140) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 4 (lambdaPow 1 (Smn 125 140)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add graded_coherence 1 4 5 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl
theorem nu_target_sphere_four_split
    (T : model.classical.sphere.Page 2 (14,139))
    (hT : IsPermanentCycle (model.classical.sphere) (14,139) T)
    (a : BiHom 125 135 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (14,139,135) (model.comparison.sphereE2 14 139 4 T) a) :
    ∃ t : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t)=T ∧ lambdaMultiply 4 t=a := by
  obtain ⟨t00,ht0⟩ := sphere_permanent_first_quotient_lift 14 139 T hT
  let t0 : BiHom 125 139 (S_0_0 : SyntheticSpectrum) := t00
  change (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0)=T at ht0
  let a0 : BiHom 125 135 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 4 t0
  have ha0 : Detects (model.convergence .sphere) (14,139,135) (model.comparison.sphereE2 14 139 4 T) a0 := by
    have h := model.sphereDetectionCompatible.homotopy_lambda 14 139 4 t0
    change Detects (model.convergence .sphere) (14,139,135)
      (sphereLabel 14 139 4 ((KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0))) (lambdaMultiply 4 t0) at h
    rw [ht0] at h
    exact h
  have hdiff : FiltrationAtLeast model.syntheticTower 15 (a-a0) :=
    detects_sub_filtration (model.convergence .sphere) (14,139,135) ha ha0
  have hnu := KIP126.Main.Internal.Selected.map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv (a-a0) hdiff
  have hlam := KIP126.Literature.Standard.selected_filtration_lambda .sphere 125 135 15 (by omega) ((a-a0)≫model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 15 ((a-a0)≫model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 5 b=(a-a0)≫model.nu.unitIso.inv at hlam
  obtain ⟨b,hb⟩ := hlam.mp hnu
  let c : BiHom 125 140 (S_0_0 : SyntheticSpectrum) := b≫model.nu.unitIso.hom
  have hc : lambdaMultiply 5 c=a-a0 := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun x=>x≫model.nu.unitIso.hom) hb
  let lc : BiHom 125 139 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 1 c
  have hq : quotientClass 1 lc=0 := by
    exact (KIP126.Main.Internal.Selected.vanishes_mod_lambda_iff_multiple 1 125 140 lc).mpr ⟨c,rfl⟩
  refine ⟨t0+lc,?_,?_⟩
  · change (KIP126.Literature.sphereFirstQuotient model) 14 139 ((t0+lc)≫XModLambdaN.incl _ 1)=T
    rw [Preadditive.add_comp,map_add]
    change (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0)+
      (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 lc)=T
    rw [ht0,hq,map_zero,add_zero]
  · let c7 : BiHom 125 135 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 5 c
    have he1 : (show BiHom 125 135 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 4 lc)=c7 :=
      lambda_four_one c
    have he : (show BiHom 125 135 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 4 (t0+lc))=a0+c7 := by
      calc
        _ = a0+(show BiHom 125 135 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 4 lc) := by
          simp only [a0,lambdaMultiply,Preadditive.comp_add]
        _ = a0+c7 := by rw [he1]
    change (show BiHom 125 135 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 4 (t0+lc))=a
    rw [he]
    have hc7 : c7=a-a0 := hc
    rw [hc7]
    abel
end
end KIP126.Main.SectionSeven.Internal
