module
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.NuNinth.Shift
import all KIP126.Main.Internal.DetectionLabels
/-! NuNinth:1198–1458, bbac1fc05843 (MIT): the actual λ⁴ inclusion,
its full finite-window comparison, and its unit-isomorphism transport. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem nu_fourth_x_detected
    (x : model.classical.sphere.Page 2 (8,130))
    (hx : x∈cycles model .sphere 5 (8,130))
    (a : BiHom 122 130 (XModLambdaN (model.nu.functor.obj SphereSpectrum) 5))
    (ha : Detects (model.convergence (.quotient 5 (.nu .sphere))) (8,130,130)
      (finiteTargetLabel model .sphere 5 8 130 0 x) a) :
    Detects (model.convergence (.quotient 9 (.nu .sphere))) (8,130,126)
      (finiteTargetLabel model .sphere 9 8 130 4 x)
      (weightShiftHom (-4) a ≫ ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) := by
  obtain ⟨e,he,aa,haa,hgr⟩ := ha
  let f := ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap
  let e' := KIP126.Literature.Standard.infinityFiniteLambda .sphere 9 4 (by decide) (8,130) 130 e
  let c : cycles model .sphere ((5:ℤ)-130+(130-(0:ℕ))) (8,130) := ⟨x,hx⟩
  have hs := (finite_target_label_iff .sphere 5 (by decide) 8 130 0 (by decide) c e).mp he
  have hh := KIP126.Literature.Standard.eInfinity_lambda_finite .sphere 9 4 (by decide) (8,130) 130 (by norm_num) e
  erw [hs] at hh
  have hre : HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj SphereSpectrum) 9) 2 (8,130,126)
      (finiteTargetLabel model .sphere 9 8 130 4 x) e' := by
    apply (finite_target_label_iff .sphere 9 (by decide) 8 130 4 (by decide) ⟨x,hx⟩ e').mpr
    exact hh
  let S := KIP126.Literature.Standard.infinityShift_comparison 4
  obtain ⟨bb,hbb,hbg⟩ := shift_graded (.quotient 5 (.nu .sphere)) (0,-4) (122,130) 8 S e aa (by
    simpa only [SyntheticTowerConvergence.filtration,Int.reduceAdd,Int.reduceSub,towerGradedIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] using hgr)
  let ee := (infinityShift model KIP126.Literature.Standard.infinityShift_comparison
    (.quotient 5 (.nu .sphere)) 4 (8,130) 130).hom e
  have hgg : ((model.convergence (.shift (0,-4) (.quotient 5 (.nu .sphere)))).identification (8,130,126)).hom ee =
      (model.convergence (.shift (0,-4) (.quotient 5 (.nu .sphere)))).filtration.toAssociatedGraded 8 (122,126) bb := by
    simpa only [SyntheticTowerConvergence.filtration,Prod.mk_add_mk,Prod.fst_add,Prod.snd_add,Int.reduceAdd,Int.reduceSub,Int.reduceNeg,Nat.cast_ofNat,ee,infinityShift,S,towerGradedIso,Iso.trans_hom,eqToIso.hom,
      eqToHom_refl,Category.id_comp,Category.comp_id] using hbg
  obtain ⟨cc,hcc,hcg⟩ := map_graded (.shift (0,-4) (.quotient 5 (.nu .sphere)))
    (.quotient 9 (.nu .sphere)) f (8,130,126) ee bb hgg
  refine ⟨e',hre,cc,?_,?_⟩
  · refine hcc.trans ?_
    have ht := hbb.trans (congrArg (shiftHomotopyClass (0,-4) _) haa)
    simpa only [f,syntheticHomotopy,SyntheticTowerConvergence.filtration,SyntheticObject.obj,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub,shiftHomotopyClass,weightShiftHom,biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      NatTrans.comp_app,eqToHom_app,eqToHom_refl,Category.id_comp] using congrArg (fun z => z ≫ f) ht
  · exact hcg

private theorem nu_fourth_y_detected
    (x : model.classical.sphere.Page 2 (11,136))
    (hx : x∈cycles model .sphere 3 (11,136))
    (a : BiHom 125 134 (XModLambdaN (model.nu.functor.obj SphereSpectrum) 5))
    (ha : Detects (model.convergence (.quotient 5 (.nu .sphere))) (11,136,134)
      (finiteTargetLabel model .sphere 5 11 136 2 x) a) :
    Detects (model.convergence (.quotient 9 (.nu .sphere))) (11,136,130)
      (finiteTargetLabel model .sphere 9 11 136 6 x)
      (weightShiftHom (-4) a ≫ ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) := by
  obtain ⟨e,he,aa,haa,hgr⟩ := ha
  let f := ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap
  let e' := KIP126.Literature.Standard.infinityFiniteLambda .sphere 9 4 (by decide) (11,136) 134 e
  let c : cycles model .sphere ((5:ℤ)-136+(136-(2:ℕ))) (11,136) := ⟨x,hx⟩
  have hs := (finite_target_label_iff .sphere 5 (by decide) 11 136 2 (by decide) c e).mp he
  have hh := KIP126.Literature.Standard.eInfinity_lambda_finite .sphere 9 4 (by decide) (11,136) 134 (by norm_num) e
  erw [hs] at hh
  have hre : HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj SphereSpectrum) 9) 2 (11,136,130)
      (finiteTargetLabel model .sphere 9 11 136 6 x) e' := by
    apply (finite_target_label_iff .sphere 9 (by decide) 11 136 6 (by decide) ⟨x,hx⟩ e').mpr
    exact hh
  let S := KIP126.Literature.Standard.infinityShift_comparison 4
  obtain ⟨bb,hbb,hbg⟩ := shift_graded (.quotient 5 (.nu .sphere)) (0,-4) (125,134) 11 S e aa (by
    simpa only [SyntheticTowerConvergence.filtration,Int.reduceAdd,Int.reduceSub,towerGradedIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] using hgr)
  let ee := (infinityShift model KIP126.Literature.Standard.infinityShift_comparison
    (.quotient 5 (.nu .sphere)) 4 (11,136) 134).hom e
  have hgg : ((model.convergence (.shift (0,-4) (.quotient 5 (.nu .sphere)))).identification (11,136,130)).hom ee =
      (model.convergence (.shift (0,-4) (.quotient 5 (.nu .sphere)))).filtration.toAssociatedGraded 11 (125,130) bb := by
    simpa only [SyntheticTowerConvergence.filtration,Prod.mk_add_mk,Prod.fst_add,Prod.snd_add,Int.reduceAdd,Int.reduceSub,Int.reduceNeg,Nat.cast_ofNat,ee,infinityShift,S,towerGradedIso,Iso.trans_hom,eqToIso.hom,
      eqToHom_refl,Category.id_comp,Category.comp_id] using hbg
  obtain ⟨cc,hcc,hcg⟩ := map_graded (.shift (0,-4) (.quotient 5 (.nu .sphere)))
    (.quotient 9 (.nu .sphere)) f (11,136,130) ee bb hgg
  refine ⟨e',hre,cc,?_,?_⟩
  · refine hcc.trans ?_
    have ht := hbb.trans (congrArg (shiftHomotopyClass (0,-4) _) haa)
    simpa only [f,syntheticHomotopy,SyntheticTowerConvergence.filtration,SyntheticObject.obj,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub,shiftHomotopyClass,weightShiftHom,biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      NatTrans.comp_app,eqToHom_app,eqToHom_refl,Category.id_comp] using congrArg (fun z => z ≫ f) ht
  · exact hcg
private theorem fourth_sphere_transport (a : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5)) :
    (weightShiftHom (-4) (a≫XModLambdaN.map model.nu.unitIso.inv 5) ≫
      ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) ≫
      XModLambdaN.map model.nu.unitIso.hom 9 =
    weightShiftHom (-4) a ≫ ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap := by
  have hn := (model.quotients.natural model.nu.unitIso.inv).lambda_naturality
    (i:=4) (j:=9) (by decide) (by decide)
  have hg : XModLambdaN.map model.nu.unitIso.inv 9 ≫ XModLambdaN.map model.nu.unitIso.hom 9 = 𝟙 _ := by
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
  change (SyntheticCategory.biShift (0,-4)).map (XModLambdaN.map model.nu.unitIso.inv 5) ≫
    ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap =
    ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap ≫
      XModLambdaN.map model.nu.unitIso.inv 9 at hn
  dsimp only [weightShiftHom]
  simp only [Functor.map_comp,Category.assoc]
  erw [reassoc_of% hn,hg,Category.comp_id]
private theorem fourth_sphere_transport_x (a : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5)) :
    (weightShiftHom (-4) (a≫XModLambdaN.map model.nu.unitIso.inv 5) ≫
      ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) ≫
      XModLambdaN.map model.nu.unitIso.hom 9 =
    weightShiftHom (-4) a ≫ ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap := by
  have hn := (model.quotients.natural model.nu.unitIso.inv).lambda_naturality
    (i:=4) (j:=9) (by decide) (by decide)
  have hg : XModLambdaN.map model.nu.unitIso.inv 9 ≫ XModLambdaN.map model.nu.unitIso.hom 9 = 𝟙 _ := by
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
  change (SyntheticCategory.biShift (0,-4)).map (XModLambdaN.map model.nu.unitIso.inv 5) ≫
    ((model.quotients.tower (model.nu.functor.obj SphereSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap =
    ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap ≫
      XModLambdaN.map model.nu.unitIso.inv 9 at hn
  dsimp only [weightShiftHom]
  simp only [Functor.map_comp,Category.assoc]
  erw [reassoc_of% hn,hg,Category.comp_id]
private theorem sphere_fourth_x_detected
    (x : model.classical.sphere.Page 2 (8,130))
    (hx : x∈cycles model .sphere 5 (8,130))
    (a : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5))
    (ha : Detects (model.convergence (.quotient 5 .sphere)) (8,130,130)
      (quotientLabel 5 8 130 0 x) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (8,130,126)
      (quotientLabel 9 8 130 4 x)
      (weightShiftHom (-4) a ≫ ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) := by
  have hn := detects_map (.quotient 5 .sphere) (.quotient 5 (.nu .sphere))
    (XModLambdaN.map model.nu.unitIso.inv 5) (8,130,130) _ a ha
  erw [sphere_quotient_label_to_nu 5 0 8 130 x] at hn
  have hp := nu_fourth_x_detected x hx (a≫XModLambdaN.map model.nu.unitIso.inv 5) hn
  have hs := detects_map (.quotient 9 (.nu .sphere)) (.quotient 9 .sphere)
    (XModLambdaN.map model.nu.unitIso.hom 9) (8,130,126) _ _ hp
  erw [sphere_quotient_label_from_nu 9 4 8 130 x,fourth_sphere_transport_x] at hs
  exact hs
private theorem sphere_fourth_y_detected
    (x : model.classical.sphere.Page 2 (11,136))
    (hx : x∈cycles model .sphere 3 (11,136))
    (a : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5))
    (ha : Detects (model.convergence (.quotient 5 .sphere)) (11,136,134)
      (quotientLabel 5 11 136 2 x) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (11,136,130)
      (quotientLabel 9 11 136 6 x)
      (weightShiftHom (-4) a ≫ ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap) := by
  have hn := detects_map (.quotient 5 .sphere) (.quotient 5 (.nu .sphere))
    (XModLambdaN.map model.nu.unitIso.inv 5) (11,136,134) _ a ha
  erw [sphere_quotient_label_to_nu 5 2 11 136 x] at hn
  have hp := nu_fourth_y_detected x hx (a≫XModLambdaN.map model.nu.unitIso.inv 5) hn
  have hs := detects_map (.quotient 9 (.nu .sphere)) (.quotient 9 .sphere)
    (XModLambdaN.map model.nu.unitIso.hom 9) (11,136,130) _ _ hp
  erw [sphere_quotient_label_from_nu 9 6 11 136 x,fourth_sphere_transport] at hs
  exact hs
end
end KIP126.Main.Internal.NuNinth
