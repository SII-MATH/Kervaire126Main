module
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.AlphaOne.Layers
import all KIP126.Main.Internal.AlphaOne.Filtration
import all KIP126.Main.Internal.AlphaOne.Corrections
import all KIP126.Main.Internal.AlphaOne.ErrorFiltration
import all KIP126.Main.Internal.AlphaOne.Classical
import all KIP126.Main.Internal.Selected.ThetaFrames

/-! The original constructive assembly for Lemma x1239,
AlphaOne/Existence.lean:2162–2245 and AlphaOne.lean:225–304,
bbac1fc05843 (MIT). All source computations and external results are called
on the same fixed system. No new paper premise is introduced. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal
open KIP126.Computation.Standard (U V correction)
open KIP126.Literature.Standard (eta syntheticH0)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private theorem theta5_square_filtration_ten
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    FiltrationAtLeast model.syntheticTower 10 (sphereProduct theta theta) :=
  Selected.stem124_weight128_filtration_ten _

private theorem theta5_square_three_cases
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    C4At theta ∨ SphereDetected 13 137 9 correction (sphereProduct theta theta) ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 10 a=sphereProduct theta theta :=
  Selected.theta_three_cases theta

private theorem ninth_quotient_stem123_weight130_filtration16_zero
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 16 a) : a=0 :=
  sphere_quotient_high_filtration_zero 9 (by decide) 123 130 16 (by decide) a ha

private theorem alpha_one_h0_filtration_seventeen
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : FiniteDetected 11 (by decide) 9 132 0 V a) :
    FiltrationAtLeast model.syntheticTower 17 (lambdaMultiply 3 (sphereAction syntheticH0 a)) :=
  alpha_h0_filtration_from_finite_window syntheticH0 V a ha

private theorem alpha_one_exists :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11), AlphaOneProperties a11 := by
  obtain ⟨a,ha11,ha9⟩ := alpha_one_detected_pair V KIP126.Computation.Standard.v_to_e12
  have hpc : IsPermanentCycle model.classical.sphere (13,137) correction := by
    obtain ⟨z,hz,_⟩ := KIP126.Computation.Standard.correction_permanent
    exact ⟨z,hz⟩
  obtain ⟨hp14,hp15⟩ := full_staircase_high_cycles
  obtain ⟨c13,hc13⟩ := sphere_permanent_first_quotient_lift 13 137 correction hpc
  obtain ⟨c14,hc14⟩ := sphere_permanent_first_quotient_lift 14 138 _ hp14
  obtain ⟨c15,hc15⟩ := sphere_permanent_first_quotient_lift 15 139 _ hp15
  obtain ⟨b,hb⟩ := eta_correction_lambda_divisible eta c13 correction
    KIP126.Literature.Standard.eta_label hc13 KIP126.Computation.Standard.h1_correction_zero
  have hU : U∈KIP126.Literature.cycles model .sphere 8 (10,134) := by
    apply KIP126.Literature.permanentCycles_le_cycles model .sphere (10,134) 8
    apply (permanent_cycle_iff_mem .sphere (10,134) U).mp
    obtain ⟨z,hz,_⟩ := KIP126.Computation.Standard.u_permanent
    exact ⟨z,hz⟩
  have hd := KIP126.Computation.Standard.d2_x125_8.toHasDifferential
  change HasDifferential model.classical.sphere 2 (8,133) (10,134) _
    (KIP126.Computation.Standard.product (r := (10,134)) KIP126.Computation.Standard.h1 V+U) at hd
  refine ⟨a,ha11,ha9,?_,?_⟩
  · intro u hu
    have herr := alpha_error_filtration_thirteen U V _ hU hd
      KIP126.Computation.Standard.e5_stem124_af11 KIP126.Computation.Standard.e4_stem124_af12 a ha11 u hu
    obtain ⟨b13,b14,b15,hbits⟩ := alpha_three_layer_restriction c13 hc13 c14 hc14 c15 hc15 _ herr
    obtain ⟨a2,a3,hs,heta⟩ := alpha_correction_sum eta c13 c14 c15 b hb b13 b14 b15
    refine ⟨a2,a3,?_,heta⟩
    have he := hbits.trans hs
    have hrho :
        ((show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from lambdaMultiply 3 (sphereAction eta a))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from lambdaMultiply 3 (quotientClass 11 u))) ≫
            (model.quotients.tower S_0_0).rho 9 11 (by decide) =
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 3
          (sphereAction eta (a ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 3 (quotientClass 9 u)) := by
      simp only [Preadditive.sub_comp,lambdaMultiply,sphereAction,quotientClass,Category.assoc,
        FiniteLambdaQuotientTower.rho_quotient]
    rw [hrho] at he
    exact sub_eq_iff_eq_add'.mp he
  · exact alpha_h0_rho_zero ninth_quotient_stem123_weight130_filtration16_zero syntheticH0 a
      (alpha_one_h0_filtration_seventeen a ha11)

end
end KIP126.Main.Internal.AlphaOne
end
