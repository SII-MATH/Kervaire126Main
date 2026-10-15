module
import all KIP126.Main.ClassicalReduction
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.AnyYPeeling
import all KIP126.Main.SectionSeven.AnyYSplit
import all KIP126.Main.SectionSeven.WeakInitialNonzero
/-! The exact bracket target, AnyYHelpers:2874–2920 at bbac1fc05843 (MIT).
Nonvanishing follows from the already established lambda-eight target argument. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
open KIP126.Literature.Standard (eta syntheticH0)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem anyy_bracket_exact_target
    (hc3:Stem126D6Vanishes) (hc5:EtaExtensionDetection)
    (a11:BiHom 123 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 11))
    (ha:AlphaOneProperties a11)
    (z:BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hz:ModuleTripleToda (lambdaMultiply 3
      (a11≫(model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z) :
    ∃ t:BiHom 125 139 (XModLambdaN (S_0_0:SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 14 139 0 T t ∧
      sphereAction syntheticH0 z=lambdaMultiply 6 t ∧ lambdaMultiply 6 t≠0 := by
  obtain ⟨u,hu,hcu⟩ := hc5
  have hp := KIP126.Computation.Standard.t_permanent_cycle
  obtain ⟨t,ht,he⟩ := anyy_sphere_exact_target_split T hp
    (lambdaMultiply 3 (sphereProduct eta u)) hcu
  have htd := model.sphereDetectionCompatible.homotopy_lambda 14 139 0 t
  change Detects (model.convergence .sphere) (14,139,139)
    (sphereLabel 14 139 0 (KIP126.Literature.sphereFirstQuotient model 14 139 (quotientClass 1 t)))
    (lambdaMultiply 0 t) at htd
  rw [ht,lambda_zero_125_139] at htd
  have htq := detects_map .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9) (14,139,139) _ _ htd
  have htn : FiniteDetected 9 (by decide) 14 139 0 T (quotientClass 9 t) := by
    apply sphere_finite_detection_nonzero 9 0 (by decide) (by decide) 14 139 T ?_ ?_ _ htq
    · exact permanentCycles_le_cycles model .sphere (14,139) _ ((permanent_cycle_iff_mem .sphere (14,139) T).mp hp)
    · intro hb
      exact survives_twelve_not_boundary_eleven .sphere (14,139) T
        (KIP126.Main.d6_vanishes_iff_target_survives_twelve.mp hc3)
        (boundaries_monotone model .sphere (14,139) (by decide) hb)
  obtain ⟨a3,hformula⟩ := anyy_toda_h0_error_formula a11 ha u hu z hz
  have heq : sphereAction syntheticH0 z=lambdaMultiply 6 (quotientClass 9 t) := by
    rw [anyy_seventh_error_zero a3,add_zero,←he] at hformula
    simpa only [lambdaMultiply,quotientClass,Category.assoc] using hformula
  refine ⟨quotientClass 9 t,htn,heq,?_⟩
  intro hzero
  apply nu_target_lambda_eight_nonzero hc3 (quotientClass 9 t) htn
  rw [←lambda_two_six_139,hzero]
  simp only [lambdaMultiply,comp_zero]
end
end KIP126.Main.SectionSeven.Internal
