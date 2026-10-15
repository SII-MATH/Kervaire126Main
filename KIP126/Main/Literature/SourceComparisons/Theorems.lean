module

public import KIP126.Main.Literature.SourceComparisons.BHS
public import KIP126.Main.Literature.SourceComparisons.RealizationKernel
public import KIP126.Main.Literature.SourceComparisons.Toda
public import KIP126.Main.Literature.SourceComparisons.May
public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Literature.AdamsSynthetic.Theorems

@[expose] public section

namespace KIP126.Main.Literature.SourceComparisons
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.SpectralSequence
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

set_option backward.isDefEq.respectTransparency false in
/-- Transport a compatible source triple along the three ACTUAL map equalities.
No statement is made about arbitrary normalized lifts. -/
theorem nuCofiber_of_source (S : NuCofiberLifts D)
    (hS : NuCofiberSourceResults D S) (B : NuCofiberLiftComparison D S) :
    NuCofiberNormalization D := by
  refine ⟨hS.nu_exponent, hS.bottom_exponent, hS.top_exponent, ?_, ?_⟩
  · simpa [sourceNormalizedNu, normalizedNu, B.nu] using hS.normalized_label
  · intro he
    change normalizedTriangle D.toAdamsComparisonData D.hopfAndDetector.nuCofiberTriangle he ∈ distTriang Syn
    have h := hS.triangle he
    convert h using 1
    simp [normalizedTriangle, sourceNormalizedTriangle, normalizedConnecting,
        sourceNormalizedConnecting, HopfAndDetectorData.nuCofiberTriangle,
        B.nu, B.bottom, B.top]

/-- Combine the source theorems with the specified completion and realization
comparisons, secondary Toda comparison and compatible ν-cofiber lifts.
The tmf survival statement is proved separately in Main. -/
theorem application_of_parts (η : BiHom 1 2 (S_0_0 : Syn)) (G : TmfDetectionClasses H)
    {background : AlgebraRealizationComparison D} (B : SourceComparisons D η G background) (A : SourceTheorems D η G B)
    (hBHS : BHSCompletionApplicability D B.bhsCompletion)
    (cBHS : BHSCompletionComparison D B.bhsCompletion)
    (rBHS : BHSRealizationComparison D B.realization B.bhsCompletion)
    (secondary : TodaSecondaryComparison η B.todaSource)
    (hnu : NuCofiberSourceResults D B.nuSource) : SourceApplicability D η G B := by
  exact ⟨hBHS, cBHS,
    realization_detection_of_completed_sources D B.realization B.bhsCompletion
      A.realization hBHS cBHS rBHS,
    may_signed_boundary_of_source B.may A.may,
    todaApplication_of_secondary η B.todaSource secondary,
    realizationKernel_of_source D B.kernelSource A.realizationKernel B.kernelComparison,
    hnu, nuCofiber_of_source D B.nuSource hnu B.nuCofiberComparison⟩

end
end KIP126.Main.Literature.SourceComparisons

/-! Literature source theorems on the fixed Adams/synthetic comparison,
using the weight-shift naturality theorem proved in Def. -/
namespace KIP126.ExternalHypotheses.LiteratureTheorems
open CategoryTheory Classical.Adams SpectralSequence
open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open KIP126.Literature.AdamsSynthetic
variable {sources : KIP126.ExternalHypotheses.LiteratureSources}

noncomputable def sourceTheorems (input : LiteratureTheorems sources)
    (shiftNatural : sources.eInftyWeightShift.Natural) :
    Literature.AdamsSynthetic.SourceTheorems standardAdamsComparison Def.standardEta
      sources.tmfLabels sources.sourceComparisons where
  classical := {
    h5Square_permanent := input.classical_h5Square_permanent
    theta5_detection := input.classical_theta5_detection
    theta5_order_two := input.classical_theta5_order_two
    stem62_exponent_two := input.classical_stem62_exponent_two
    theta5_filtration_gap := input.classical_theta5_filtration_gap
    two_detection := input.classical_two_detection
    eta_detection := input.classical_eta_detection
    nu_detection := input.classical_nu_detection
    eta_permanent := input.classical_eta_permanent
    nu_permanent := input.classical_nu_permanent
  }
  bx := input.bxTheta
  synthetic := {
    lifts := {
      nu_cofiber := input.synthetic_nu_cofiber
      lift := input.synthetic_lift
      triangle_lift := input.synthetic_triangle_lift
    }
    finite_lift := input.synthetic_finite_lift
    bockstein := input.synthetic_bockstein
    permanent_lift := input.synthetic_permanent_lift
    differentials := input.synthetic_differentials
    filtration_lambda := input.synthetic_filtration_lambda
    e2_weight_vanishing := input.synthetic_e2_weight_vanishing
    finite_quotient_page_vanishing := input.synthetic_finite_quotient_page_vanishing
    eInfty := {
      presentation := sources.eInftyPresentation
      weightShift := sources.eInftyWeightShift
      maps := {
        shift_natural := shiftNatural
        lambda_nu := input.eInfty_lambda_nu
        lambda_finite := input.eInfty_lambda_finite
        rho_finite := input.eInfty_rho_finite
        rho_nu := input.eInfty_rho_nu
      }
      labels := input.eInfty_labels
    }
  }
  realizationKernel := input.realizationKernel
  realization := by
    intro X products applicability convergence
    exact {
      lifetime := input.realization_lifetime X products applicability convergence
      detection := input.realization_detection X products applicability convergence
      prescribed_lift := input.realization_prescribed_lift X products applicability convergence
      boundary_lift := input.realization_boundary_lift X products applicability convergence
    }
  may := input.mayPushpull
  toda := {
    h0_label := input.toda_h0_label
    lambda_h0 := input.toda_lambda_h0
    h0_eta := input.toda_h0_eta
    low_indeterminacy := input.toda_low_indeterminacy
  }
  tmf := {
    connective := input.tmf_connective
    finiteMod2Type := input.tmf_finiteMod2Type
    standard_labels := input.tmf_standard_labels
    vanishing62 := input.tmf_vanishing62
    low_filtration63 := input.tmf_low_filtration63
    kappaBar_detection := input.tmf_kappaBar_detection
    w_detection := input.tmf_w_detection
    high125_nonzero := input.tmf_high125_nonzero
  }


end KIP126.ExternalHypotheses.LiteratureTheorems
