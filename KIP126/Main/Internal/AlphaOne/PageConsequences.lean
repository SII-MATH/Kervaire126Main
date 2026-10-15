module
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.AlphaOne.LastDifferential

/-! All finite-differential and rho-target consequences in
AlphaOne.lean:75–168, bbac1fc05843 (MIT), on the fixed actual quotients. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ninth_quotient_error_d3 :
    FiniteNonzeroDifferential 9 3 13 137 16 139 6 8
      (product h4 (atom .x_109_12)) (product h1 (atom .x_122_15_2)) :=
  finite_last_nonzero 9 3 6 (by decide) (by decide) 13 137 _ _ d3_h4_x109_12

private theorem eleventh_quotient_candidate_d7 :
    FiniteNonzeroDifferential 11 7 11 134 18 140 4 10
      d7Source (product h1 (atom .x_121_17)) :=
  finite_last_nonzero 11 7 4 (by decide) (by decide) 11 134 _ _ d7_source

private theorem eleventh_quotient_candidate_d3 :
    FiniteNonzeroDifferential 11 3 15 138 18 140 8 10
      (product h0Square (atom .x_123_13_2)) (product h0Square (atom .x_122_16)) :=
  finite_last_nonzero 11 3 8 (by decide) (by decide) 15 138 _ _ d3_h0Square_x123_13_2

private theorem sphere_quotient_page_zero (q : ℕ) (hq : 0<q)
    (r s t w : ℤ) (hr : 2≤r) (hwindow : t<w ∨ (q:ℤ)≤t-w) :
    Subsingleton ((model.family.quotient (S_0_0 : SyntheticSpectrum) q).Page r (s,t,w)) := by
  let Q := model.quotients.functoriality.functor q
  let e := model.family.functor.mapIso (Q.mapIso model.nu.unitIso)
  have hz := KIP126.Literature.Standard.finite_quotient_vanishing .sphere q hq r hr s t w (by omega)
  let i := e.inv.pageMap r (s,t,w)
  let j := e.hom.pageMap r (s,t,w)
  have hij : i ≫ j=𝟙 _ := by
    dsimp only [i,j]
    rw [←SpectralSequenceMorphism.pageMap_comp,e.inv_hom_id,SpectralSequenceMorphism.pageMap_id]
  have hi : Function.Injective i := by
    intro x y hxy
    have h := congrArg j hxy
    simpa only [←CategoryTheory.comp_apply,hij,ModuleCat.id_apply] using h
  have hs : Subsingleton (((model.family.functor.obj
      (XModLambdaN (model.nu.functor.obj SphereSpectrum) q)).Page r (s,t,w)) : ModuleCat ℤ) := by
    have hh := ModuleCat.isZero_iff_subsingleton.mp hz
    simpa only [Page,model.family.firstPage,SyntheticAdamsFamily.quotient,
      SyntheticAdamsFamily.obj,SyntheticAdamsSS.Page,ClassicalObject.obj] using hh
  have ht : Subsingleton (((model.family.functor.obj
      (XModLambdaN (S_0_0 : SyntheticSpectrum) q)).Page r (s,t,w)) : ModuleCat ℤ) :=
    ⟨fun x y => hi (hs.elim _ _)⟩
  simpa only [Page,model.family.firstPage,SyntheticAdamsFamily.quotient,
    SyntheticAdamsFamily.obj,SyntheticAdamsSS.Page,ClassicalObject.obj] using ht

private theorem ninth_quotient_candidate_target_zero (r : ℤ) (hr : 2≤r) :
    Subsingleton ((model.family.quotient (S_0_0 : SyntheticSpectrum) 9).Page r (18,140,130)) :=
  sphere_quotient_page_zero 9 (by decide) r 18 140 130 hr (Or.inr (by decide))

private theorem rho_to_ninth_kills_candidate_target (r : ℤ) (hr : 2≤r)
    (y : (model.family.quotient (S_0_0 : SyntheticSpectrum) 11).Page r (18,140,130)) :
    familyPageMap model.family ((model.quotients.tower S_0_0).rho 9 11 (by decide)) r (18,140,130) y=0 :=
  (ninth_quotient_candidate_target_zero r hr).elim _ _
end
end KIP126.Main.Internal.AlphaOne
end
