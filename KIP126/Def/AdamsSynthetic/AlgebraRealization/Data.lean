module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements

@[expose] public section

/-! The mathematical algebra/realization comparison context, before any external
Moss theorem or program-coordinate result is supplied. -/

namespace KIP126.AdamsSynthetic

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : KIP126.Classical.Adams.MilnorCooperations H}

/-- Structural comparisons on the same Adams context: realization, tensor
algebras, boundary conventions and tower comparisons. No source theorem,
identification with literature objects, computational coordinates or Main conclusion
is included. The fixed background assumption supplies these structural
properties on the same explicitly selected synthetic objects. -/
structure AlgebraRealizationComparison (D : AdamsComparison H M Syn) where
  realization : KIP126.Literature.AdamsSynthetic.RealizationCoordinates D
  algebra : KIP126.Literature.AdamsSynthetic.AdamsAlgebraStructures D
  quotientCompatibility : KIP126.Literature.AdamsSynthetic.QuotientAlgebraCompatibility D algebra
  algebraDetectionCompatibility : KIP126.Literature.AdamsSynthetic.AlgebraDetectionCompatibility D algebra
  may : KIP126.Literature.AdamsSynthetic.MayContext Syn
  realizationAdditive : D.recovery.realization.Additive
  weights : KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison D.nu D.recovery
  nuE2 :
    letI := algebra.classicalSymmetric
    letI := algebra.syntheticSymmetric
    letI := algebra.realizationMonoidal.realization
    letI := realizationAdditive
    KIP126.Comparison.ClassicalSynthetic.RealizationTower.NuE2RealizationCompatibility D
      (fun X a w => KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison.doubleShift
        D.nu D.recovery weights (X.obj D.hopfAndDetector) a (-w))

end KIP126.AdamsSynthetic
