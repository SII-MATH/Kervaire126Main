module
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.Theta.TodaExistence
import all KIP126.Main.Internal.Theta.TodaAlgebra
import all KIP126.Main.Internal.Theta.TodaIndeterminacy
import all KIP126.Main.Internal.Theta.Detection
import all KIP126.Main.Internal.Theta.ZeroDegree

/-! The original final assembly of Lemma 7.16,
Section7/ThetaToda.lean:1400–1430 and ThetaShuffle.lean:637–653,
bbac1fc05843 (MIT). It constructs a bracket using the lambda cofiber and
identifies its full first-quotient indeterminacy through the selected
quotient algebra. The archived unused route_moss gap is not an input. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal KIP126.Main.Internal.Theta KIP126.Literature.Route
open KIP126.Computation.Standard (product h6 atom)
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive := model.exactness.shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem synthetic_theta_b_toda
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    ∃ (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) (z : BiHom 125 134 (S_0_0 : SyntheticSpectrum)),
      SphereDetected 8 70 0 (atom .b) b ∧
      SphereDetected 9 134 0 (product (r := (9,134)) h6 (atom .b)) z ∧
      TripleToda theta syntheticTwo b z := by
  obtain ⟨b,hb⟩ := sphere_permanent_first_quotient_lift 8 70 (atom .b) b_permanent_from_inputs
  obtain ⟨z,hz⟩ := synthetic_theta_b_bracket_nonempty model.quotients.coherence theta b
    (Choice.theta_degree_order_two theta) (two_torsion_62_70 b)
  obtain ⟨q,hq,hql⟩ := theta_b_algebra_toda_candidate KIP126.Literature.Standard.mayData
    (zero_hom_nonzero_unique zero_nonzero_unique) KIP126.Literature.Standard.syntheticH0 theta
    KIP126.Literature.Standard.toda_h0_label htheta KIP126.Literature.Standard.toda_lambda_h0
    (Choice.theta_degree_order_two theta) b
  let src := tripleTodaSource (Syn := SyntheticSpectrum) 62 64 0 0 62 70
  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (62,70)
  have hg : (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0 : SyntheticSpectrum)≫F.map syntheticTwo =
      2 • 𝟙 (Smn (Syn := SyntheticSpectrum) 62 70) := by
    have hc := model.quotients.coherence.left_unit (62,70) (S_0_0 : SyntheticSpectrum)
    change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _=_ at hc
    have he : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0 : SyntheticSpectrum)=
        F.map (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,F] using hc
    dsimp only [syntheticTwo]
    rw [Functor.map_comp,←he,←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    simp only [Functor.map_nsmul]
    change 2 • F.map (𝟙 (S_0_0 : SyntheticSpectrum))=2 • 𝟙 (F.obj (S_0_0 : SyntheticSpectrum))
    rw [CategoryTheory.Functor.map_id]
  have hzr : Toda.Relation (src.inv≫quotientClass 1 z) (F.map theta)
      (2 • 𝟙 (Smn (Syn := SyntheticSpectrum) 62 70)) (quotientClass 1 b) := by
    have ht := hz
    change Toda.Relation (src.inv≫z) (F.map theta)
      ((SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0 : SyntheticSpectrum)≫F.map syntheticTwo) b at ht
    rw [hg] at ht
    simpa only [quotientClass,Category.assoc] using Toda.postcompose ht (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1)
  have hqz : quotientClass 1 z=q := by
    apply (cancel_epi src.inv).mp
    exact theta_b_quotient_toda_unique theta htheta b _ _ hzr hq
  refine ⟨b,z,?_⟩
  apply theta_b_bracket_label_suffices theta b z
    (sphere_zero_weight_nonzero_detection_8_70 _ b hb b_nonzero_from_inputs) hz
  rw [hqz,hql,hb]

private theorem theta_b_multiplied_shuffle
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) (z : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hz : TripleToda theta syntheticTwo b z) :
    lambdaMultiply 2 (sphereProduct KIP126.Literature.Standard.syntheticH0 z) =
      lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta (sphereProduct theta b)) :=
  KIP126.Main.Internal.Theta.theta_b_multiplied_shuffle theta htheta b z hz

end
end KIP126.Main.SectionSeven.Internal
