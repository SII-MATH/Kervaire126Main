module

public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Literature.Background.SphereConvergence
public import KIP126.Literature.Standard.ClassicalContext
public import KIP126.Def.StableHomotopy.FiniteType.Predicates
public import KIP126.Def.StableHomotopy.Context.Proofs
public import KIP126.Def.StableHomotopy.Context.Mapping.Data
public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

/-! BHS theorems and comparison with completed objects.

The statements retain the hypotheses of BHS A.1(2) and cor:tau-surj
(Source/BHS/source/SynRevBigraded.tex and SynRevAdams.tex). Completion maps
and their image, divisibility and realization comparisons transport the
source theorems. Specialization to the sphere uses Literature's accepted
standard-sphere applicability hypothesis; source nilpotent completeness
and strong convergence remain explicit.
-/
namespace KIP126.Main.Literature.SourceComparisons
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic

section Transport
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Transport source lifetime/detection and the two existential lift clauses.
The hypotheses contain actual q/νq maps, canonical detection comparison,
realization naturality, and the precise prescribed/torsion image reflections.
The proof uses λ naturality and the source clauses; it never calls a paper
proposition, ExternalHypotheses, or a high125 conclusion. -/
theorem realization_detection_of_completed_sources
    (D : AdamsComparison H M Syn) (R : RealizationCoordinates D) (Q : BHSCompletionData D)
    (source : BHSRealizationSourceResults D R)
    (applicable : BHSCompletionApplicability D Q)
    (comparison : BHSCompletionComparison D Q)
    (realization : BHSRealizationComparison D R Q) : RealizationDetection D R := by
  constructor
  · intro X s t r hr x a hx hs ha
    have h := (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).lifetime s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((comparison.permanent_cycles X s t x).mp hx)
      ((realization.survives_to X s t r x).mp hs)
      (realization.first_quotient_natural X s t x a ha)
    intro hz
    apply h
    simpa only [lambdaMultiply, Category.assoc, zero_comp] using
      congrArg (fun z => z ≫ (SyntheticCategory.biShift (0,0)).map
        (D.nu.functor.map (Q.map X))) hz
  · intro X s t x a hx ha
    apply (realization.detection X s t x (realizeNuZero D R X a)).mpr
    rw [realization.realization_natural]
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).detection s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((realization.nonzero_survival X s t x).mp hx)
      (realization.first_quotient_natural X s t x a ha)
  · intro X s t x α hx hα
    apply realization.prescribed_lift_reflection X s t x α
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).prescribed_lift s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) (α ≫ Q.map X)
      ((realization.nonzero_survival X s t x).mp hx)
      ((realization.detection X s t x α).mp hα)
  · intro X s t r hr y hy hh
    apply realization.torsion_lift_reflection X s t (r-1) y
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).boundary_lift s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) y)
      ((comparison.permanent_cycles X s t y).mp hy)
      ((realization.hit_on_page X s t r y).mp hh)
end Transport

end KIP126.Main.Literature.SourceComparisons
