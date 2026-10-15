module

public import KIP126.Literature.AdamsSynthetic.Statements

@[expose] public section

/-! Classical/synthetic comparison hypotheses for the generalized extension laws.
The E∞ formulas retain their λ, ρ and class compatibility; the lifting,
realization and May statements use the same categories and functors.
Defining these structures neither proves them nor assumes the extension laws. -/

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS A.9/A.11 with the compatible E∞ formulas on the SAME family.
All label, λ and ρ compatibility is part of the supplied source application.
No unrelated E∞ equivalences may be inserted as substitutes. -/
structure EInftyComparison where
  presentation : KIP126.Literature.AdamsSynthetic.EInftyPresentation D
  weightShift : EInftyWeightShift D.family
  maps : KIP126.Literature.AdamsSynthetic.EInftyMapCompatibility D presentation weightShift
  labels : KIP126.Literature.AdamsSynthetic.EInftyLabelAgreement D presentation

/-- Lifting, convergence, realization and filtration comparisons for the same
Adams towers. Their truth is supplied by the literature hypotheses; no
generalized extension law is a field of this structure. -/
structure SyntheticComparisonTheorems where
  lifts : KIP126.Literature.AdamsSynthetic.SyntheticLiftTheorems D
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  permanent_lift : PermanentLiftCriterion D
  differentials : DifferentialRigidity D
  eInfty : EInftyComparison D
  realization_kernel : RealizationKernel D
  filtration_lambda : FiltrationLambda D
  e2_weight_vanishing : E2WeightVanishing D
  finite_quotient_page_vanishing : FiniteQuotientPageVanishing D

end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Applied May input, retaining the source sign and the fixed conventions.
Removing the sign requires the corresponding exponent-two condition. Mod-two E₂ coordinates alone do not prove such a condition on
homotopy groups. -/
structure MayBoundaryFormula extends MayContext Syn where
  boundary : toMayContext.SignedBoundary

end KIP126.Literature.AdamsSynthetic
