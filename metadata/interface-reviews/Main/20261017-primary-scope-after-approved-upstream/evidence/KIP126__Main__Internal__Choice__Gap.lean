module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Choice.Filtration

/-! The filtration gap for two theta choices, from Selected/ChoiceInvariance:743–854
at bbac1fc05843 (MIT). Vanishing quotient pages are computed by Main. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem theta_choice_filtration_gap_of_pages
    (hpages : Subsingleton (model.classical.sphere.Page 3 (3,65)) ∧
      Subsingleton (model.classical.sphere.Page 3 (4,66)) ∧
      Subsingleton (model.classical.sphere.Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (hθ : ThetaChoice θ) (hθ' : ThetaChoice θ') :
    FiltrationAtLeast model.syntheticTower 6 (θ-θ') := by
  classical
  have hlambda0 (a : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : lambdaMultiply 0 a=a := by
    have hc := model.quotients.coherence.right_unit (62,64) (S_0_0 : SyntheticSpectrum)
    have he : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn 62 64 : SyntheticSpectrum) := by
      change (biShiftAddIso (62,64) (0,0) (62,64) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient 2 64 (quotientClass 1 θ) = _ at hθ
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient 2 64 (quotientClass 1 θ') = _ at hθ'
  have ht := model.sphereDetectionCompatible.homotopy_lambda 2 64 0 θ
  have ht' := model.sphereDetectionCompatible.homotopy_lambda 2 64 0 θ'
  rw [hlambda0,hθ] at ht
  rw [hlambda0,hθ'] at ht'
  have h3 : FiltrationAtLeast model.syntheticTower 3 (θ-θ') :=
    detects_sub_filtration (model.convergence .sphere) (2,64,64) ht ht'
  have hzero (j : ℤ) (hj : 3 ≤ j) (hj' : j < 6) :
      IsZero ((model.family.obj (S_0_0 : SyntheticSpectrum)).sequence.ssData (j,62+j,64)).eInfty := by
    have hp : Subsingleton (KIP126.Literature.PermanentQuotient model .sphere
        (1+(62+j)-64) (j,62+j)) := by
      interval_cases j
      · exact permanentQuotient_zero_of_page_zero .sphere 3 2 (3,65) (by omega) (by omega) hpages.1
      · exact permanentQuotient_zero_of_page_zero .sphere 3 3 (4,66) (by omega) (by omega) hpages.2.1
      · exact permanentQuotient_zero_of_page_zero .sphere 4 4 (5,67) (by omega) (by omega) hpages.2.2
    let e := KIP126.Literature.Standard.infinityNuWindow .sphere (j,62+j) 64 (by omega)
    haveI : Subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty) :=
      ⟨fun x y => e.injective (@Subsingleton.elim _ hp _ _)⟩
    let hnu := ModuleCat.isZero_of_subsingleton
      (((model.family.nu model.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty)
    let f := (model.family.functor.map model.nu.unitIso.hom).eInftyMap (j,62+j,64)
    let g := (model.family.functor.map model.nu.unitIso.inv).eInftyMap (j,62+j,64)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have h4 := filtration_step_of_infinity_zero (model.convergence .sphere)
    3 62 64 (hzero 3 (by omega) (by omega)) (θ-θ') h3
  have h5 := filtration_step_of_infinity_zero (model.convergence .sphere)
    4 62 64 (hzero 4 (by omega) (by omega)) (θ-θ') h4
  exact filtration_step_of_infinity_zero (model.convergence .sphere)
    5 62 64 (hzero 5 (by omega) (by omega)) (θ-θ') h5

end
end KIP126.Main.Internal.Choice
end
