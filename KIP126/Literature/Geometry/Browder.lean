module

public import KIP126.Literature.Geometry.KervaireInvariant
public import KIP126.AdamsSynthetic

/-! Browder's geometric criterion, as used in AimPaper Theorem 1.3.
This independent literature input does not import Main or Geometry. The
source-to-model proof must relate actual stable framings to the fixed
2-completed sphere Adams spectral sequence, including the comparison from
integral framed cobordism and the specified standard Milnor h_j classes.
The geometric dimension convention is 4k+2, so j starts at 1, not 0.
-/

@[expose] section
namespace KIP126.Literature.Geometry
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

/-- Browder's criterion (AimPaper Theorem 1.3), with its positive-index
convention explicit. Survival is nonzero survival of the specified standard
square on the actual fixed sphere, not just vanishing outgoing differentials.
Pending proof: Browder's theorem and its geometric/source-to-model comparison. -/
public theorem browder_iff (n : ℕ) :
    KervaireInvariantOneExists n ↔
      ∃ j : ℕ, 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧
        NonzeroSurvival model.classical.sphere (2, ((2 ^ (j + 1) : ℕ) : ℤ))
          (model.standardClasses.standardHiSquare j) := by
  sorry

end KIP126.Literature.Geometry
