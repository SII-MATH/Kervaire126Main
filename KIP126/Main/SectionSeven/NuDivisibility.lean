module

public import KIP126.Main.Computation.LowDegrees
public import KIP126.Main.SectionSeven.NuExtension.NinthQuotient
public import KIP126.Main.SectionSeven.ThetaToda
public import KIP126.Main.SectionSeven.ThetaShuffle
public import KIP126.Main.SectionSeven.H0Extension.RepresentativeCalculus
public import KIP126.Main.SectionSeven.TodaNonempty
public import KIP126.Main.SectionSeven.TodaNonvanishing
public import KIP126.Main.SectionSeven.FiltrationElevenRepresentative
public import KIP126.Main.SectionSeven.FiltrationElevenDetection
public import KIP126.Main.SectionSeven.NuDivisibility.Filtration
public import KIP126.Main.SectionSeven.AlphaOne

-- The following lemmas provide the representative and filtration calculations.
import all KIP126.Main.SectionSeven.H0Extension.RepresentativeCalculus
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.SectionSeven.TodaNonvanishing
import all KIP126.Main.SectionSeven.FiltrationElevenRepresentative
import all KIP126.Main.SectionSeven.FiltrationElevenDetection
import all KIP126.Main.SectionSeven.NuDivisibility.Filtration

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison
local notation "M" => standardMilnorCooperations
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

attribute [local irreducible] KIP126.LinE2.homogeneousPart

open private anyy_eta_unique_from_low_degrees anyy_bracket_exact_target
  from KIP126.Main.SectionSeven.H0Extension.RepresentativeCalculus
open private main_module_toda_nonempty_of_alpha
  from KIP126.Main.SectionSeven.TodaNonempty
open private toda_representative_lambda_two_h0_nonzero
  from KIP126.Main.SectionSeven.TodaNonvanishing
open private exists_filtration_eleven_representative
  from KIP126.Main.SectionSeven.FiltrationElevenRepresentative
open private y_detected_of_filtration_bounds
  from KIP126.Main.SectionSeven.FiltrationElevenDetection
open private nu_target_full_of_nonzero
  from KIP126.Main.SectionSeven.NuDivisibility.Filtration

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- `prop:state5false`: choose a bracket member, remove its AF7 and AF9
components while preserving its nonzero lambda-squared h0 product, and
apply the actual ninth-quotient nu extension and the P/Q lifting argument. -/
theorem target_nu_divisible
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M (D).toAdamsComparisonData L η) :
    TargetNuDivisible D ((L).target M) h2 := by
  let SF := KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing
  obtain ⟨a11,ha⟩ := lemma_7_14_alpha_one_exists
  obtain ⟨z,hz⟩ := main_module_toda_nonempty_of_alpha D η h₀ ((L).U M) eV
    literatureTheorems.toda.eta_squared a11 ha
  have unique := anyy_eta_unique_from_low_degrees literatureTheorems.synthetic.eInfty
    sphereVanishing
    (KIP126.Main.Computation.sphere_eta_nonzero_unique KIP126.Main.externalHypotheses)
    (KIP126.Main.Computation.sphere_e2_two_three_subsingleton KIP126.Main.externalHypotheses)
  obtain ⟨t,ht,he,_⟩ := anyy_bracket_exact_target I SF
    literatureTheorems.synthetic literatureTheorems.realization unique η h₀
    literatureTheorems.toda.eta_squared literatureTheorems.toda.low_indeterminacy
    eV hc3 hc5 a11 ha z hz
  have hzn := toda_representative_lambda_two_h0_nonzero I SF literatureTheorems.synthetic.eInfty
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.quotientCompatibility
    literature.sources.sourceComparisons.algebraDetectionCompatibility hc3 h₀ z t ht he
  obtain ⟨theta,hcriterion,_,_⟩ := literatureTheorems.bx
  have htheta : ThetaChoice M (D).toAdamsComparisonData theta := hcriterion.2.1
  obtain ⟨b,zTheta,hb,hzTheta,hToda⟩ := synthetic_theta_b_toda theta htheta
  have hlabel := (I).products ⟨1,64,8,70⟩
    (by simp [KIP126.Computation.SphereAndCofiber.Raw.products]) KIP126.LinE2.dataH6 KIP126.Computation.Near126.B
  dsimp only at hlabel
  rw [(I).distinguishedClasses.h6] at hlabel
  have hzTheta' : SphereDetected D 9 134 0
      ((I).interpretation.sphere 9 134
        (KIP126.LinE2.mulAt KIP126.LinE2.dataH6 KIP126.Computation.Near126.B)) zTheta := by
    rw [hlabel]
    exact hzTheta
  obtain ⟨y,hf,hn⟩ := exists_filtration_eleven_representative I literatureTheorems.synthetic
    literatureTheorems.realization SF classical_stem124_af13_generated
    η literatureTheorems.classical.hopf.1 h₀ theta htheta b hb zTheta hzTheta'
    (theta_b_multiplied_shuffle theta htheta b zTheta hToda) z hzn
  have hy := y_detected_of_filtration_bounds I literatureTheorems.synthetic.eInfty
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.algebraDetectionCompatibility
    η literatureTheorems.toda y hf hn
  exact nu_target_full_of_nonzero I literatureTheorems.synthetic SF
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.quotientCompatibility
    literature.sources.sourceComparisons.algebraDetectionCompatibility h2
    literatureTheorems.applicability.nuCofiber.normalized_label h₀
    literatureTheorems.toda.h0_label literatureTheorems.toda.lambda_h0
    lemma_7_20_nu_extension y hy.1 hn

end
end KIP126.Main.SectionSeven
