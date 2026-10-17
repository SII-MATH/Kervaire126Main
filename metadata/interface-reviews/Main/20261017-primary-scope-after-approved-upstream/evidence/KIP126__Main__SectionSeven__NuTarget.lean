module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.Conditions
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.NormalizedNu
public import KIP126.Main.SectionSeven.Indeterminacy
import all KIP126.Main.Internal.NuNinth.Assembly
import all KIP126.Main.SectionSeven.ThetaToda
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.WeakRepresentative
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.SectionSeven.NuTargetFull
/-! Proposition 7.9's divisibility step.
Source: Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/NuTarget.lean:61–104
(MIT; see the retained source LICENSE).
The original argument is assembled from the migrated AlphaOne, Toda,
ninth-quotient ν, and P/Q proofs on the fixed public upstream objects. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Literature.Route KIP126.Main.Internal
open KIP126.Main.SectionSeven.Internal
open KIP126.Literature.Standard (eta syntheticH0)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
/-- The P and Q branches give the exact λν divisibility equation for the
fixed target class, under the genuine Stem126D6Vanishes and EtaExtensionDetection hypotheses. -/
private theorem target_nu_divisible (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection) :
    TargetNuDivisible T hopfNu := by
  obtain ⟨a11,ha⟩ := AlphaOne.alpha_one_exists
  obtain ⟨z,hz⟩ := module_toda_nonempty_of_alpha a11 ha
  obtain ⟨t,ht,he,_⟩ := anyy_bracket_exact_target hc3 hc5 a11 ha z hz
  have hzn := weak_initial_twice_h0_nonzero hc3 syntheticH0 z t ht he
  let theta := KIP126.Literature.Standard.bxTheta5
  have htheta : ThetaChoice theta := KIP126.Literature.Standard.bx_theta_label
  obtain ⟨b,zTheta,hb,hzTheta,hToda⟩ := synthetic_theta_b_toda theta htheta
  obtain ⟨y,hf,hn⟩ := main_weak_high_representative eta KIP126.Literature.Standard.eta_label
    syntheticH0 theta htheta b hb zTheta hzTheta (theta_b_multiplied_shuffle theta htheta b zTheta hToda) z hzn
  have hd := model.sphereDetectionCompatible.homotopy_lambda 1 1 0 syntheticH0
  change Detects (model.convergence .sphere) (1,1,1)
    (sphereLabel 1 1 0 (KIP126.Literature.sphereFirstQuotient model 1 1 (quotientClass 1 syntheticH0)))
    (lambdaMultiply 0 syntheticH0) at hd
  have hh0 : KIP126.Literature.sphereFirstQuotient model 1 1 (quotientClass 1 syntheticH0)=KIP126.Computation.Standard.h0 := KIP126.Literature.Standard.toda_h0_label
  rw [hh0,lambda_zero_0_1] at hd
  have hy := weak_y_detected_of_f11_and_nonzero syntheticH0 hd y hf hn
  exact nu_target_full_of_nonzero hopfNu KIP126.Literature.Standard.nuCofiber_normalized_label
    syntheticH0 KIP126.Literature.Standard.toda_h0_label
    KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient y hy.1 hn
end
end KIP126.Main.SectionSeven
