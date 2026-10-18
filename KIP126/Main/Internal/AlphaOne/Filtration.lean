module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.ProofTools.Operations
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.AlphaOne.FiniteWindow

/-! AlphaOne/Filtration.lean:44–124, pinned bbac1fc05843 (MIT).
The finite quotient calculations raise the original F10 bound to F17. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
private theorem alpha_h0_filtration_from_finite_window
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (x : model.classical.sphere.Page 2 (9,132))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : FiniteDetected 11 (by decide) 9 132 0 x a) :
    FiltrationAtLeast model.syntheticTower 17
      (lambdaMultiply 3 (sphereAction h0 a)) := by
  have alpha_h0_initial_filtration
      (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
      (x : model.classical.sphere.Page 2 (9,132))
      (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
      (ha : FiniteDetected 11 (by decide) 9 132 0 x a) :
      FiltrationAtLeast model.syntheticTower 10
        (lambdaMultiply 3 (sphereAction h0 a)) := by
    have hlam : lambdaMultiply 0 h0=h0 := by
      have hc := model.quotients.coherence.right_unit (0,1) (S_0_0 : SyntheticSpectrum)
      have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
          SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : SyntheticSpectrum) := by
        change (biShiftAddIso (0,1) (0,0) (0,1) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ h0=h0
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hh := model.sphereDetectionCompatible.homotopy_lambda 1 1 0 h0
    rw [hlam] at hh
    obtain ⟨_,_,h,hval,_⟩ := hh
    have hf0 : FiltrationAtLeast model.syntheticTower 1 h0 := by
      have hm : ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 1 (0,1)).arrow h ∈
          ModuleCat.subobjectModule _ ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 1 (0,1)) := ⟨h,rfl⟩
      change ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 1 (0,1)).arrow h=h0 at hval
      rw [hval] at hm
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    obtain ⟨_,_,a',ha',_⟩ := ha.1
    have hfa : FiltrationAtLeast model.syntheticTower 9 a := by
      have hm : ((model.syntheticTower.filtration (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)).F 9 (123,132)).arrow a' ∈
          ModuleCat.subobjectModule _ ((model.syntheticTower.filtration (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)).F 9 (123,132)) := ⟨a',rfl⟩
      change ((model.syntheticTower.filtration (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)).F 9 (123,132)).arrow a'=a at ha'
      rw [ha'] at hm
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    have hf := KIP126.Literature.Standard.action_filtration (.quotient 11 .sphere) 0 1 123 132 1 9 h0 a hf0 hfa
    obtain ⟨z,hz⟩ := hf
    refine ⟨lambdaMultiply 3 z,?_⟩
    change lambdaMultiply 3 z ≫ (model.syntheticTower.tower _).projection 10 = _
    change z ≫ (model.syntheticTower.tower _).projection 10 = sphereAction h0 a at hz
    dsimp only [lambdaMultiply]
    simp only [Category.assoc,hz]
  have alpha_filtration_gap
      (hfinite : ∀ s : ℤ, 10≤s → s≤16 → Subsingleton
        (KIP126.Literature.CycleQuotient model .sphere (18-s) (s-6) (s,s+123)))
      (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) :
      FiltrationAtLeast model.syntheticTower 10 a ↔
        FiltrationAtLeast model.syntheticTower 17 a := by
    apply filtration_iff_of_infinity_zero (model.convergence (.quotient 11 .sphere))
      10 17 123 130 (by decide)
    intro j hj hj'
    haveI : Subsingleton (KIP126.Literature.CycleQuotient model .sphere
        (11-(123+j)+130) (1+(123+j)-130) (j,123+j)) := by
      rw [show (11:ℤ)-(123+j)+130=18-j by omega,
        show (1:ℤ)+(123+j)-130=j-6 by omega,add_comm 123 j]
      exact hfinite j hj (by omega)
    let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide) (j,123+j) 130
      (by constructor <;> omega)
    haveI : Subsingleton (((model.family.quotient (model.nu.functor.obj SphereSpectrum) 11).sequence.ssData (j,123+j,130)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((model.family.quotient (model.nu.functor.obj SphereSpectrum) 11).sequence.ssData (j,123+j,130)).eInfty)
    let f := (model.family.functor.map (XModLambdaN.map model.nu.unitIso.hom 11)).eInftyMap (j,123+j,130)
    let g := (model.family.functor.map (XModLambdaN.map model.nu.unitIso.inv 11)).eInftyMap (j,123+j,130)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←model.quotients.functoriality.map_comp,model.nu.unitIso.inv_hom_id,
        model.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact (alpha_filtration_gap stem123_weight130_actual_finite_quotients _).mp
    (alpha_h0_initial_filtration h0 x a ha)
end
end KIP126.Main.Internal.AlphaOne
end
