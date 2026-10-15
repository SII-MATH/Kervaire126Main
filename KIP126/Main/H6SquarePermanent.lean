module

public import KIP126.Main.PropositionSevenEight
public import KIP126.Literature.Standard.Sphere.Classes
public import KIP126.Def.SpectralSequence.Permanence.Predicates

@[expose] public section

/-! LWX Theorem 7.1 (`thm:126survives`).

Proposition 7.8 reduces failure of permanence to three conditions;
Proposition 7.9 excludes their conjunction. Both results concern the same
standard sphere and the same external literature and computation hypotheses.
The theorem inherits the recorded background axioms and the remaining MH2
proof obligation in the generalized Mahowald argument.
-/
namespace KIP126.Main

open KIP126.Classical.Adams KIP126.SpectralSequence

/-- LWX Theorem 7.1. The standard h₆² has a common Z∞ representative projecting to it on E₂,
whose E∞ image is nonzero, in bidegree (s,t) = (2,128). -/
theorem h6_sq_permanent :
    NonzeroSurvival sphereAdamsData (2, 128) standardH6Square := by
  exact KIP126.Main.h6_square_permanent_of_differential_criterion_and_eta_obstruction
    standardMilnorCooperations KIP126.Main.AdamsSynthetic.adamsComparison
    KIP126.Main.AdamsSynthetic.sphereClasses KIP126.Main.AdamsSynthetic.etaClass
    KIP126.Main.AdamsSynthetic.literatureTheorems.classical.hopf.1
    (KIP126.Main.proposition_7_8 KIP126.Main.externalHypotheses)
    KIP126.Main.SectionSeven.DifferentialCriterion.eta_extension_excluded_of_d6_vanishes

end KIP126.Main
