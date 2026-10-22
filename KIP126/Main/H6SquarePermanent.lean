module

public import KIP126.Main.DifferentialCriterion
import all KIP126.Main.SectionSeven.Final
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

private theorem fixed_h6_sq_permanent :
    NonzeroSurvival model.classical.sphere (2,128)
      model.standardClasses.standardH6Square := by
  obtain ⟨cases, criteria⟩ := h6_square_differential_dichotomy_and_criterion
  rcases cases with h | h
  · exact h.1
  · obtain ⟨h3, _, h5⟩ := criteria.mp h.1
    exact False.elim (eta_extension_excluded_of_d6_vanishes h3 h5)

/-- LWX Theorem 7.1 for any nonzero standard-class family on the fixed actual
sphere E₂ page, retaining a common Z∞ representative and nonzero E∞ image. -/
public theorem h6_sq_permanent
    (H : KIP126.Classical.Adams.StandardSphereClasses
      model.classical model.sphereAlgebra) :
    NonzeroSurvival model.classical.sphere (2,128)
      (model.sphereAlgebra.product (1,64) (1,64) (H.hi 6) (H.hi 6)) := by
  have hh : H.hi 6 = KIP126.Computation.Standard.h6 := by
    rcases KIP126.Computation.Standard.h6_exhaustive (H.hi 6) with h | h
    · exact (H.hi_ne_zero 6 h).elim
    · exact h
  rw [hh]
  exact fixed_h6_sq_permanent

end KIP126.Main
