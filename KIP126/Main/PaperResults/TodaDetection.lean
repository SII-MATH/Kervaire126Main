module

import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.Internal.FiniteReflection
import all KIP126.Main.PaperResults.TodaFiltration
import all KIP126.Main.PaperResults.TodaSmallQuotient

/-! Auxiliary constructions for the complete detection of the actual
alpha-one Toda bracket. Quotient restriction retains the specified member. -/

@[expose] section
namespace KIP126.Main.Paper.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.ProofTools.Operations
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta syntheticH0)
open KIP126.Literature.Route
open KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem relation_right_zero_factors
    {X Y Z W : SyntheticSpectrum} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hx : Toda.Relation x f g (0 : Z ⟶ W)) :
    ∃ y : Y⟦(1 : ℤ)⟧ ⟶ W, x = f⟦(1 : ℤ)⟧' ≫ y := by
  obtain ⟨Q, i, p, hT, gbar, hg, hpx⟩ := hx
  have hp : p ≫ x = 0 := by simpa only [comp_zero] using hpx
  have hrot : (Triangle.mk f i p).rotate ∈ distTriang SyntheticSpectrum :=
    rot_of_distTriang (Triangle.mk f i p) hT
  obtain ⟨y, hy⟩ := (Triangle.mk f i p).rotate.yoneda_exact₃ hrot x hp
  exact ⟨-y, by simpa [Triangle.rotate] using hy⟩

private theorem eta_indeterminacy_normalize
    (coh:BiShiftCoherence SyntheticSpectrum) (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum))
    {W:SyntheticSpectrum} (y:(Smn (Syn:=SyntheticSpectrum) 123 130)⟦(1:ℤ)⟧⟶W) :
    (tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129).hom≫
      ((SyntheticCategory.biShift (123,130)).map eta)⟦(1:ℤ)⟧'≫y =
    sphereAction eta
      ((SyntheticCategory.biShift_comp (123,130) (1,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 123 130)≫y) := by
  have hc:=coh.associativity (1,2) (123,130) (1,0) (124,132) (124,130) (125,132)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:SyntheticSpectrum)
  have hi :
      ((SyntheticCategory.biShift (1,0)).mapIso
        ((SyntheticCategory.biShift_comp (1,2) (123,130)).app (S_0_0:SyntheticSpectrum))) ≪≫
        (SyntheticCategory.biShift_comp (124,132) (1,0)).app (S_0_0:SyntheticSpectrum) =
      (SyntheticCategory.biShift_comp (123,130) (1,0)).app (Smn (Syn:=SyntheticSpectrum) 1 2) ≪≫
        (SyntheticCategory.biShift_comp (1,2) (124,130)).app (S_0_0:SyntheticSpectrum) := by
    apply Iso.ext
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn,Functor.mapIso_hom,Iso.app_hom] using hc
  have hinv:=congrArg (fun e=>e.inv) hi
  simp only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] at hinv
  have hn:=(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    ((SyntheticCategory.biShift (123,130)).map eta)
  have hn':=(SyntheticCategory.biShift_comp (Syn:=SyntheticSpectrum) (123,130) (1,0)).inv.naturality eta
  change ((SyntheticCategory.biShift_comp (124,132) (1,0)).inv.app (S_0_0:SyntheticSpectrum) ≫
    (SyntheticCategory.biShift (1,0)).map
      ((SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:SyntheticSpectrum)) ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app
      ((SyntheticCategory.biShift (123,130)).obj (Smn 1 2))) ≫
    ((SyntheticCategory.biShift (123,130)).map eta)⟦(1:ℤ)⟧'≫y =
    (SyntheticCategory.biShift_comp (1,2) (124,130)).inv.app (S_0_0:SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (124,130)).map eta≫
      (SyntheticCategory.biShift_comp (123,130) (1,0)).inv.app (S_0_0:SyntheticSpectrum)≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 123 130)≫y
  have hny:=congrArg (fun z=>z≫y) hn
  simp only [Category.assoc] at hny
  simp only [Category.assoc]
  rw [←hny]
  simp only [←Category.assoc]
  rw [hinv]
  simpa only [Category.assoc,Functor.comp_map,Prod.mk_add_mk,Int.reduceAdd,Smn] using congrArg (fun z =>
    (SyntheticCategory.biShift_comp (1,2) (124,130)).inv.app (S_0_0:SyntheticSpectrum) ≫ z ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 123 130) ≫ y) hn'.symm

private theorem zero_source_toda_eta_image
    {X : SyntheticSpectrum} (z : BiHom 125 132 X)
    (hz : ModuleTripleToda (0 : BiHom 123 129 X) syntheticH0 eta z) :
    ∃ a : BiHom 124 130 X, z = sphereAction eta a := by
  let src := tripleTodaSource (Syn := SyntheticSpectrum) 1 2 0 1 123 129
  change Toda.Relation (src.inv ≫ z)
    ((SyntheticCategory.biShift (123,130)).map eta) _ 0 at hz
  obtain ⟨y, hy⟩ := relation_right_zero_factors hz
  have he := congrArg (fun a => src.hom ≫ a) hy
  simp only [src.hom_inv_id_assoc] at he
  refine ⟨(SyntheticCategory.biShift_comp (123,130) (1,0)).inv.app
      (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).hom.app
        (Smn 123 130) ≫ y, ?_⟩
  exact he.trans (eta_indeterminacy_normalize model.quotients.coherence eta y)

private theorem alpha_three_restrict_three_zero
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : AlphaOneProperties a11) :
    lambdaMultiply 3 (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)) ≫
      (model.quotients.tower S_0_0).rho 3 9 (by decide) = 0 := by
  have hf := detected_filtration (.quotient 9 .sphere) (9,132,132) ha.2.1.1
  have hl := lambda_filtration_preserved 3 9 _ hf
  have hm := map_filtration (.quotient 9 .sphere) (.quotient 3 .sphere)
    ((model.quotients.tower S_0_0).rho 3 9 (by decide)) _ hl
  exact sphere_quotient_high_filtration_zero 3 (by decide) 123 129 9 (by decide) _ hm

private theorem alpha_toda_restrict_three_eta_image
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : AlphaOneProperties a11)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hz : ModuleTripleToda (lambdaMultiply 3
      (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)))
      syntheticH0 eta z) :
    ∃ a : BiHom 124 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3),
      z ≫ (model.quotients.tower S_0_0).rho 3 9 (by decide) = sphereAction eta a := by
  apply zero_source_toda_eta_image
  have hzero := alpha_three_restrict_three_zero a11 ha
  have hr := Toda.postcompose hz ((model.quotients.tower S_0_0).rho 3 9 (by decide))
  rw [hzero] at hr
  simpa only [ModuleTripleToda, homotopyRegrade, eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat, Int.reduceSub] using hr

/-- All members of the specified bracket have the same actual image in Q3.
This uses the Q9 indeterminacy, not arbitrary eta multiples in Q3. -/
private theorem alpha_toda_restrict_three_unique
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : AlphaOneProperties a11)
    (z₁ z₂ : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (h₁ : ModuleTripleToda (lambdaMultiply 3
      (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)))
      syntheticH0 eta z₁)
    (h₂ : ModuleTripleToda (lambdaMultiply 3
      (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)))
      syntheticH0 eta z₂) :
    z₁ ≫ (model.quotients.tower S_0_0).rho 3 9 (by decide) =
      z₂ ≫ (model.quotients.tower S_0_0).rho 3 9 (by decide) := by
  let src := tripleTodaSource (Syn := SyntheticSpectrum) 1 2 0 1 123 129
  let rho := (model.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 3 9 (by decide)
  let a := lambdaMultiply 3 (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))
  change Toda.Relation (src.inv ≫ z₁)
    ((SyntheticCategory.biShift (123,130)).map eta) _ a at h₁
  change Toda.Relation (src.inv ≫ z₂)
    ((SyntheticCategory.biShift (123,130)).map eta) _ a at h₂
  obtain ⟨y,v,h⟩ := (Toda.relation_iff_indeterminacy h₂).mp h₁
  have haz : a ≫ rho = 0 := alpha_three_restrict_three_zero a11 ha
  let b : BiHom 124 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) :=
    (SyntheticCategory.biShift_comp (123,130) (1,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).hom.app (Smn 123 130) ≫ y
  have hb : sphereAction eta b ≫ rho = 0 := by
    apply sphere_quotient_high_filtration_zero 3 (by decide) 125 132 11 (by decide)
    exact map_filtration (.quotient 9 .sphere) (.quotient 3 .sphere) rho _
      (eta_ninth_stem124_weight130_filtration_eleven b)
  have he : src.hom ≫ ((SyntheticCategory.biShift (123,130)).map eta)⟦(1:ℤ)⟧' ≫ y =
      sphereAction eta b := eta_indeterminacy_normalize model.quotients.coherence eta y
  have hh := congrArg (fun k => src.hom ≫ k ≫ rho) h
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_sub,
    Category.assoc, src.hom_inv_id_assoc, haz, comp_zero, add_zero] at hh
  have he' := congrArg (fun k => k ≫ rho) he
  simp only [Category.assoc] at he'
  rw [he', hb] at hh
  exact sub_eq_zero.mp hh

/-- Exact reduction of the paper's full detection statement to the actual
Q3 image of the specified bracket member. No Q3 vanishing is assumed here. -/
private theorem alpha_toda_detected_iff_restrict_three_zero
    (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : AlphaOneProperties a11)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hz : ModuleTripleToda (lambdaMultiply 3
      (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)))
      syntheticH0 eta z) :
    FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y z ↔
      z ≫ (model.quotients.tower S_0_0).rho 3 9 (by decide) = 0 := by
  constructor
  · intro hd
    apply sphere_quotient_high_filtration_zero 3 (by decide) 125 132 11 (by decide)
    exact map_filtration (.quotient 9 .sphere) (.quotient 3 .sphere)
      ((model.quotients.tower S_0_0).rho 3 9 (by decide)) _
      (detected_filtration (.quotient 9 .sphere) (11,136,132) hd.1)
  · intro hr
    have hf : FiltrationAtLeast model.syntheticTower 11 z := by
      apply ninth_stem125_weight132_filtration_eleven_of_third z
      rw [hr]
      exact (model.syntheticTower.filtrationSubmodule _ 10 (125,132)).zero_mem
    obtain ⟨t, ht, he, _⟩ := anyy_bracket_exact_target hc3 hc5 a11 ha z hz
    have hn := weak_initial_twice_h0_nonzero hc3 syntheticH0 z t ht he
    have hd := model.sphereDetectionCompatible.homotopy_lambda 1 1 0 syntheticH0
    change Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 (KIP126.Literature.sphereFirstQuotient model 1 1
        (quotientClass 1 syntheticH0))) (lambdaMultiply 0 syntheticH0) at hd
    have hh0 : KIP126.Literature.sphereFirstQuotient model 1 1 (quotientClass 1 syntheticH0) =
        KIP126.Computation.Standard.h0 := KIP126.Literature.Standard.toda_h0_label
    have hzero : lambdaMultiply 0 syntheticH0 = syntheticH0 := by
      have hc := model.quotients.coherence.right_unit (0,1) (S_0_0 : SyntheticSpectrum)
      have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) =
          SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : SyntheticSpectrum) := by
        change (biShiftAddIso (0,1) (0,0) (0,1) (by simp)).hom.app _ = _ at hc
        simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
          eqToHom_app, eqToHom_refl, Category.comp_id, Smn] using hc
      dsimp only [lambdaMultiply, lambdaPow]
      simp only [eqToHom_refl, Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫
          syntheticH0 = syntheticH0
      rw [←Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [hh0, hzero] at hd
    exact weak_y_detected_of_f11_and_nonzero syntheticH0 hd z hf hn

end
end KIP126.Main.Paper.Internal
