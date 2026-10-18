module
import all KIP126.Main.SectionSeven.Predicates

import all KIP126.Main.SectionSeven.AlphaOne
/-! Existence of the module Toda bracket from the actual annihilation
relation, ported from Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/TodaNonempty.lean (MIT; see the retained source LICENSE).
The fixed upstream h₀η relation and coherent shifts suffice for existence;
identifying a particular bracket value remains a separate paper step. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Literature.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  graded_shiftAdditive p
local notation "eta" => KIP126.Literature.Standard.eta
local notation "h0" => KIP126.Literature.Standard.syntheticH0

private theorem module_toda_nonempty {X : SyntheticSpectrum}
    (a : BiHom 123 132 X) (ha : lambdaMultiply 3 (sphereAction h0 a) = 0) :
    ∃ z : BiHom 125 132 X, ModuleTripleToda (lambdaMultiply 3 a) h0 eta z := by
  have shift_assoc_inv (coh : BiShiftCoherence SyntheticSpectrum)
      (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (habc : ab+c=total) (habc' : a+bc=total) (A : SyntheticSpectrum) :
      (biShiftAddIso ab c total habc).inv.app A ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
      (biShiftAddIso a bc total habc').inv.app A ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
    have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
        (biShiftAddIso ab c total habc).app A) =
      ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
        (biShiftAddIso a bc total habc').app A) :=
      Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
    have hi := congrArg Iso.inv he
    exact hi
  have h0_action_lambda_three (etaAux : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
      {X : SyntheticSpectrum} (c : BiHom 123 132 X) :
      sphereAction etaAux (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction etaAux c) := by
    have ha := shift_assoc_inv graded_coherence (0,1) (123,132) (0,-3)
      (123,133) (123,129) (123,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
      Int.reduceSub, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 3
      ((SyntheticCategory.biShift_comp (0,1) (123,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
    erw [← reassoc_of% (lambdaPow_naturality 3
      ((SyntheticCategory.biShift (123,132)).map etaAux))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (123,132) (0,-3)).inv.naturality etaAux)]
    rfl
  have hzero : sphereProduct eta h0 = 0 := by
    have hc := model.sphereProductCommutative 1 2 0 1 eta h0
    norm_num [homotopyRegrade] at hc
    rw [hc]
    exact KIP126.Literature.Standard.toda_h0_eta
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
  let f:= (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,130)).map eta
  let g:= (SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app (S_0_0:SyntheticSpectrum)≫F.map h0
  have hfg:f≫g=0 := by
    have hh:=congrArg F.map hzero
    dsimp only [sphereProduct] at hh
    simp only [Functor.map_comp,Functor.map_zero] at hh
    have hh':F.map ((SyntheticCategory.biShift (0,1)).map eta)≫F.map h0=0 := by
      apply (cancel_epi (F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum)))).mp
      simpa only [comp_zero] using hh
    have hn:=((SyntheticCategory.biShift_comp (0,1) (123,129)).inv.naturality eta)
    calc
      _ = (SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app (Smn 1 2)≫
          F.map ((SyntheticCategory.biShift (0,1)).map eta)≫F.map h0 := by
        simpa only [f,g,F,Category.assoc,Functor.comp_map,Prod.mk_add_mk,Int.reduceAdd] using
          congrArg (fun z => z≫F.map h0) hn
      _ = 0 := by rw [hh',comp_zero]
  have hga:g≫lambdaMultiply 3 a=0 := by
    simpa only [g,F,sphereAction,Category.assoc,Nat.cast_ofNat,Int.reduceSub] using
      (h0_action_lambda_three h0 a).trans ha
  obtain ⟨v,hv⟩:=Toda.exists_relation f g (lambdaMultiply 3 a) hfg hga
  let src:=tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129
  refine ⟨src.hom≫v,?_⟩
  change Toda.Relation (src.inv≫(src.hom≫v)) f g (lambdaMultiply 3 a)
  simpa only [src.inv_hom_id_assoc] using hv

/-- The compatible alpha₁ supplies the annihilation relation needed for
this actual Q9 bracket; no bracket value is selected in advance. -/
private theorem module_toda_nonempty_of_alpha
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : AlphaOneProperties a11) :
    let a9 := a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)
    ∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h0 eta z := by
  exact module_toda_nonempty _ ha.2.2.2

end
end KIP126.Main.SectionSeven
