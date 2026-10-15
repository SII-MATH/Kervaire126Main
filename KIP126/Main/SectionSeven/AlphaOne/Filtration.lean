module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Computation.Hypotheses
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates

import all KIP126.Main.SectionSeven.AlphaOne.FiniteWindow

@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven

open private stem123_weight130_finite_quotients from KIP126.Main.SectionSeven.AlphaOne.FiniteWindow
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

section AlphaH0Filtration
open CategoryTheory.Limits KIP126.Computation.SphereAndCofiber
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
private theorem alpha_h0_filtration_from_finite_window (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
    (BHS : SyntheticComparisonTheorems D') (algebra : AdamsAlgebraStructures D') (compatibility : AlgebraDetectionCompatibility D' algebra)
    (h0 : BiHom 0 1 (S_0_0 : Syn)) (x : E2 H SphereSpectrum 9 132)
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiniteDetected D' 11 (by decide) 9 132 0 x a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 17
      (lambdaMultiply 3 (sphereAction h0 a)) := by
  have alpha_h0_initial_filtration
      (algebra : AdamsAlgebraStructures D') (compatibility : AlgebraDetectionCompatibility D' algebra)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      (x : E2 H SphereSpectrum 9 132)
      (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
      (ha : FiniteDetected D' 11 (by decide) 9 132 0 x a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10
        (lambdaMultiply 3 (sphereAction h0 a)) := by
    have hlam : lambdaMultiply 0 h0=h0 := by
      have hc := D'.shiftCoherence.right_unit (0,1) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : Syn) := by
        change (biShiftAddIso (0,1) (0,0) (0,1) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn) ≫ h0=h0
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hh := D'.comparisonCompatible.homotopy_lambda 1 1 0 h0
    rw [hlam] at hh
    obtain ⟨_,_,h,hval,_⟩ := hh
    have hf0 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 1 h0 := by
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)).arrow h ∈
          ModuleCat.subobjectModule _ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)) := ⟨h,rfl⟩
      change ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)).arrow h=h0 at hval
      rw [hval] at hm
      simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    obtain ⟨_,_,a',ha',_⟩ := ha.1
    have hfa : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a := by
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)).arrow a' ∈
          ModuleCat.subobjectModule _ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)) := ⟨a',rfl⟩
      change ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)).arrow a'=a at ha'
      rw [ha'] at hm
      simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    have hf := compatibility.action_filtration (.quotient 11 .sphere) 0 1 123 132 1 9 h0 a hf0 hfa
    obtain ⟨z,hz⟩ := hf
    refine ⟨lambdaMultiply 3 z,?_⟩
    change lambdaMultiply 3 z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 10 _ = _
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 10 _ = sphereAction h0 a at hz
    dsimp only [lambdaMultiply]
    simp only [Category.assoc,hz]
  have alpha_filtration_gap
      (BHS : SyntheticComparisonTheorems D')
      (hfinite : ∀ s : ℤ, 10≤s → s≤16 → Subsingleton
        (PageRepresentatives.CycleQuotient H SphereSpectrum (18-s) (s-6) (s,s+123)))
      (a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 11)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 17 a := by
    apply (D'.quotientConvergence 11 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      10 17 123 130 (by decide)
    intro j hj hj'
    haveI : Subsingleton (PageRepresentatives.CycleQuotient H SphereSpectrum
        (11-(123+j)+130) (1+(123+j)-130) (j,123+j)) := by
      rw [show (11:ℤ)-(123+j)+130=18-j by omega,
        show (1:ℤ)+(123+j)-130=j-6 by omega,add_comm 123 j]
      exact hfinite j hj (by omega)
    let e := BHS.eInfty.presentation.finiteWindow SphereSpectrum 11 (by decide) (j,123+j) 130
      (by constructor <;> omega)
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum 11).sequence.ssData (j,123+j,130)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum 11).sequence.ssData (j,123+j,130)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom 11)).eInftyMap (j,123+j,130)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv 11)).eInftyMap (j,123+j,130)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact (alpha_filtration_gap BHS (stem123_weight130_finite_quotients I) _).mp
    (alpha_h0_initial_filtration algebra compatibility h0 x a ha)
end AlphaH0Filtration

end
end KIP126.Main.SectionSeven
