module
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Literature.Standard.Secondary
import all KIP126.Main.SectionSeven.AnyYShuffle
/-! Lambda coherence and the exact bracket error formula,
AnyYHelpers:2207–2288 at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Literature.Route KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Literature.Standard (eta syntheticH0)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private theorem y_detection_toda_main_eta_right_three     (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 124 134 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,134) (0,-3)
    (125,136) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (124,134)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.naturality η)]
  rfl


private theorem y_detection_toda_main_eta_right_six     (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 124 137 X) :
    sphereAction η (lambdaMultiply 6 c) = lambdaMultiply 6 (sphereAction η c) := by
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,137) (0,-6)
    (125,139) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (1,2) (124,137)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift (124,137)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,137) (0,-6)).inv.naturality η)]
  rfl


private theorem y_detection_toda_main_lambda_six_one     {X:SyntheticSpectrum} (c : BiHom 125 140 X) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  have ha := shift_assoc_inv model.quotients.coherence (125,140) (0,-1) (0,-6)
    (125,139) (0,-7) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (125,140) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 125 140)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 1 6 7 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl



theorem anyy_toda_h0_error_formula
    (a11:BiHom 123 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 11))
    (ha:AlphaOneProperties a11)
    (u:BiHom 124 134 (S_0_0:SyntheticSpectrum)) (hu:SphereDetected 10 134 0 KIP126.Computation.Standard.U u)
    (z:BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hz:ModuleTripleToda (lambdaMultiply 3 (a11≫(model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z) :
    ∃a3:BiHom 125 140 (XModLambdaN (S_0_0:SyntheticSpectrum) 9),
      sphereAction syntheticH0 z=(show BiHom 125 133 (XModLambdaN (S_0_0:SyntheticSpectrum) 9) from
        quotientClass 9 (lambdaMultiply 3 (sphereProduct eta u)))+
        (show BiHom 125 133 (XModLambdaN (S_0_0:SyntheticSpectrum) 9) from lambdaMultiply 7 a3) := by
  obtain ⟨a2,a3,hr,he⟩:=ha.2.2.1 u hu
  refine ⟨a3,?_⟩
  rw [y_detection_toda_main_toda_h0_relation eta_unique_from_low_degrees eta syntheticH0
    KIP126.Literature.Standard.toda_eta_squared KIP126.Literature.Standard.toda_low_indeterminacy _ ha.2.2.2 z hz,hr]
  have hadd (v w:BiHom 124 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 9)):
      sphereAction eta (v+w)=sphereAction eta v+sphereAction eta w := by
    simp only [sphereAction,Preadditive.comp_add]
  rw [hadd,y_detection_toda_main_eta_right_three,y_detection_toda_main_eta_right_six,he,y_detection_toda_main_lambda_six_one]
  congr 1
  simp only [quotientClass,sphereProduct,sphereAction,lambdaMultiply,Category.assoc]
end
end KIP126.Main.SectionSeven.Internal
