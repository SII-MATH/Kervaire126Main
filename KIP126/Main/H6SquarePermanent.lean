module

public import KIP126.Main.DifferentialCriterion
public import KIP126.Main.SectionSeven.Final

/-! The final proof follows bbac1fc05843 Main/Solution/h6_sq_permanent and
DifferentialReduction/Conclusion (MIT; see the retained source LICENSE). Upstream facts are directly
callable. There is no Challenge, result package or extra acceptance premise.
The theorem still depends on the separately tracked upstream and paper gaps.
-/

@[expose] section
namespace KIP126.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

public theorem eta_extension_excluded_of_d6_vanishes : Stem126D6Vanishes → ¬ EtaExtensionDetection :=
  SectionSeven.eta_extension_excluded_of_d6_vanishes

/-- LWX Theorem 7.1, retaining the common Z∞ representative and nonzero
E∞ image of the actual product h6*h6 in the fixed sphere sequence. -/
public theorem h6_sq_permanent :
    NonzeroSurvival model.classical.sphere (2,128)
      model.standardClasses.standardH6Square := by
  obtain ⟨cases, criteria⟩ := h6_square_differential_dichotomy_and_criterion
  rcases cases with h | h
  · exact h.1
  · obtain ⟨h3, _, h5⟩ := criteria.mp h.1
    exact False.elim (eta_extension_excluded_of_d6_vanishes h3 h5)

end KIP126.Main
