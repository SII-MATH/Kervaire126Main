module
import all KIP126.Main.Internal.NuNinth.Incoming
public import KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.NuNinth.Fourth
import all KIP126.Main.Internal.NuNinth.Unit
import all KIP126.Main.Internal.NuNinth.Frames
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.SectionSeven.WeakInitialNonzero
/-! NuNinth:1774–1942, bbac1fc05843 (MIT): λ⁴ push and the AF12/13
correction, retaining both nonzero detection conclusions. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.Literature KIP126.ProofTools
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal KIP126.Main.SectionSeven
open KIP126.Main.Internal.Selected.NuError KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
private def fourth_push {m w : ℤ} {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-4)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-4) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-4)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-4)).map a ≫ f
private theorem nu_fourth_push {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-4)).obj X ⟶ Y)
    (ν : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) (x : BiHom 122 130 X) :
    sphereAction ν (fourth_push f x) = fourth_push f (sphereAction ν x) := by
  have ha := Selected.shift_assoc_inv model.quotients.coherence (3,4) (122,130) (0,-4)
    (125,134) (122,126) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  simp only [fourth_push, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (3,4) (122,126)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (122,126)).map ν ≫
      ((SyntheticCategory.biShift_comp (122,130) (0,-4)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (0,-4)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,134) (0,-4)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-4)).map
        ((SyntheticCategory.biShift_comp (3,4) (122,130)).inv.app (S_0_0 : SyntheticSpectrum) ≫
          (SyntheticCategory.biShift (122,130)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (122,130) (0,-4)).inv.naturality ν)]
  erw [← reassoc_of% ha]
private theorem nu5_push_relation
    (ν : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (x : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5))
    (y : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5))
    (h : sphereAction ν x = y) :
    sphereAction ν
      (fourth_push ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
        (i := 4) (j := 9) (by decide) (by decide)).lambdaMap x) =
    fourth_push ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
      (i := 4) (j := 9) (by decide) (by decide)).lambdaMap y := by
  rw [nu_fourth_push, h]
private theorem nu_ninth_of_fifth_weak
    (ν : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (h5 : NuExtension5 (KIP126.Computation.Standard.X)
      (KIP126.Computation.Standard.Y) ν) :
    ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      Detects (model.convergence (.quotient 9 .sphere)) (8,130,126)
        (quotientLabel 9 8 130 4 (KIP126.Computation.Standard.X)) x ∧
      Detects (model.convergence (.quotient 9 .sphere)) (11,136,131)
        (quotientLabel 9 11 136 5 (KIP126.Computation.Standard.Y)) y ∧
      sphereAction ν x = lambdaMultiply 1 y := by
  let X := KIP126.Computation.Standard.X
  let Y := KIP126.Computation.Standard.Y
  obtain ⟨x5,y5,hx5,hy5,hxy⟩ := h5
  have hX : X ∈ cycles model .sphere 5 (8,130) := by
    obtain ⟨x,hx,hxn⟩ := KIP126.Computation.Standard.x_to_e6
    exact ((isCycle_iff_reaches model .sphere 6 (by decide) (8,130) X).mpr ⟨x,hx⟩).2
  have hY : Y ∈ cycles model .sphere 4 (11,136) := by
    obtain ⟨y,hy,hyn⟩ := KIP126.Computation.Standard.y_to_e5
    exact ((isCycle_iff_reaches model .sphere 5 (by decide) (11,136) Y).mpr ⟨y,hy⟩).2
  let f := ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=4) (j:=9) (by decide) (by decide)).lambdaMap
  let x9 : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := weightShiftHom (-4) x5 ≫ f
  let yp : BiHom 125 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := weightShiftHom (-4) y5 ≫ f
  have hx9 := sphere_fourth_x_detected X hX x5 hx5.1
  have hyp := sphere_fourth_y_detected Y
    (cycles_antitone model .sphere (11,136) (by decide : (3:ℤ)≤4) hY) y5 hy5.1
  obtain ⟨y0,hy⟩ := sphere_finite_detection_exists_weak 9 5 (by decide) (by decide) 11 136 ⟨Y,hY⟩
  let y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := y0
  let ly : BiHom 125 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := lambdaMultiply 1 y
  have hly := NuNinth.lambda_one_finite_detected_136 Y y hy
  have herr12 : FiltrationAtLeast model.syntheticTower 12 (yp-ly) :=
    detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (11,136,130) hyp hly
  have herr13 := (nu_nine_af12_gap (yp-ly)).mp herr12
  have hb1 := nu9_error_data.2.1
  obtain ⟨c0,hc⟩ := sphere_finite_detection_exists_weak 9 7 (by decide) (by decide) 13 138
    ⟨KIP126.Computation.Table.basis .sphere 13 138 1,hb1⟩
  let c : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := c0
  let lc : BiHom 125 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := lambdaMultiply 1 c
  have hlc := NuNinth.lambda_one_finite_detected_138 (KIP126.Computation.Table.basis .sphere 13 138 1) c hc
  obtain ⟨b,hb⟩ := finite_detection_peel 9 (13,138,130)
    (quotientLabel 9 13 138 8 (KIP126.Computation.Table.basis .sphere 13 138 1))
    (nu_nine_af13_frame) (lc) hlc (yp-ly) herr13
  have hz := sphere_quotient_high_filtration_zero 9 (by decide) 125 130 14 (by decide)
    ((yp-ly)-(if b then lc else 0)) hb
  let y9 : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := y+(if b then c else 0)
  have heq : yp=lambdaMultiply 1 y9 := by
    have hh := sub_eq_zero.mp hz
    change yp-ly=(if b then lc else 0) at hh
    have hyadd : lambdaMultiply 1 y9=ly+(if b then lc else 0) := by
      cases b <;> simp only [y9,ly,lc,lambdaMultiply,Bool.false_eq_true,↓reduceIte,
        add_zero,Preadditive.comp_add]
    rw [hyadd]
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
  have hc13 : FiltrationAtLeast model.syntheticTower 13 c :=
    detected_filtration (.quotient 9 .sphere) (13,138,131) hc
  have hc12 : FiltrationAtLeast model.syntheticTower 12 c :=
    model.syntheticTower.filtrationSubmodule_antitone _ (125,131) (by decide : (12:ℤ)≤13) hc13
  have hy9 : Detects (model.convergence (.quotient 9 .sphere)) (11,136,131)
      (quotientLabel 9 11 136 5 Y) y9 := by
    apply Choice.detects_of_difference_in_next_filtration (model.convergence (.quotient 9 .sphere))
      (11,136,131) (a:=y) (b:=y9) hy
    cases b
    · change FiltrationAtLeast model.syntheticTower 12 (show BiHom 125 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 9) from (y+0)-y)
      rw [add_zero,sub_self]
      exact (model.syntheticTower.filtrationSubmodule _ 12 (125,131)).zero_mem
    · change FiltrationAtLeast model.syntheticTower 12 ((y+c)-y)
      rw [add_sub_cancel_left]
      exact hc12
  refine ⟨x9,y9,hx9,hy9,?_⟩
  have hpush := nu5_push_relation ν x5 y5 hxy
  have hs : sphereAction ν x9=yp := by
    simpa only [x9,yp,f,weightShiftHom,fourth_push,biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,
      eqToIso.inv,eqToHom_app,eqToHom_refl,Category.id_comp,Category.assoc] using hpush
  exact hs.trans heq
private theorem nu_ninth_of_fifth_complete
    (ν : BiHom 3 4 (S_0_0:SyntheticSpectrum))
    (h5 : NuExtension5 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y ν) :
    NuExtension9 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y ν := by
  obtain ⟨x,y,hx,hy,hxy⟩ := nu_ninth_of_fifth_weak ν h5
  let X := KIP126.Computation.Standard.X
  let Y := KIP126.Computation.Standard.Y
  obtain ⟨x6,hx6,hx6n⟩ := KIP126.Computation.Standard.x_to_e6
  obtain ⟨y5,hy5,hy5n⟩ := KIP126.Computation.Standard.y_to_e5
  have hX : X∈cycles model .sphere 5 (8,130) :=
    ((isCycle_iff_reaches model .sphere 6 (by decide) (8,130) X).mpr ⟨x6,hx6⟩).2
  have hY : Y∈cycles model .sphere 4 (11,136) :=
    ((isCycle_iff_reaches model .sphere 5 (by decide) (11,136) Y).mpr ⟨y5,hy5⟩).2
  have hXn : X≠0 := by
    intro hh
    change RepresentsOnPage model.classical.sphere 6 (8,130) X x6 at hx6
    rw [hh] at hx6
    exact hx6n (represents_unique hx6 (RepresentsOnPage.zero (by decide)))
  have hYn : Y≠0 := by
    intro hh
    change RepresentsOnPage model.classical.sphere 5 (11,136) Y y5 at hy5
    rw [hh] at hy5
    exact hy5n (represents_unique hy5 (RepresentsOnPage.zero (by decide)))
  have hXb : X∉boundaries model .sphere 5 (8,130) :=
    nu9_not_boundary .sphere (8,130) X hXn 5 (by decide)
      ⟨by decide, by decide, fun r hr _ => KIP126.Computation.Standard.x_not_hit.not_hit hr⟩
  have hYb : Y∉boundaries model .sphere 6 (11,136) :=
    nu9_not_boundary .sphere (11,136) Y hYn 6 (by decide) y_not_hit_through_six
  refine ⟨x,y,?_,?_,hxy⟩
  · exact sphere_finite_detection_nonzero 9 4 (by decide) (by decide) 8 130 X hX hXb x hx
  · exact sphere_finite_detection_nonzero 9 5 (by decide) (by decide) 11 136 Y hY hYb y hy
end
end KIP126.Main.Internal.NuNinth
