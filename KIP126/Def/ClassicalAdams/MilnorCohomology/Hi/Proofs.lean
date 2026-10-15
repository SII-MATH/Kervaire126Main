module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Vanishing.Proofs

@[expose] public section


/-! Nonvanishing of the actual primitive hᵢ family, independently of Lin data.
In filtration one the preceding positive-degree cochain space is zero. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Every primitive hᵢ cochain has a nonzero polynomial value. -/
theorem hiCochain_ne_zero (i : ℕ) : hiCochain i ≠ 0 := by
  intro h
  have hp : hiPolynomial i = 0 := congrArg Subtype.val h
  exact (pow_ne_zero _ (MvPolynomial.X_ne_zero (0, 0))) hp

/-- The actual cobar class hᵢ is not an incoming boundary. -/
theorem hi_ne_zero (i : ℕ) : hi H M i ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := (hi_eq_zero_iff H M i).mp h
  letI := cochains_zero_length_subsingleton (2 ^ i) (by positivity)
  have hb0 : b = 0 := Subsingleton.elim _ _
  apply hiCochain_ne_zero i
  simpa only [hb0, map_zero] using hb.symm

/-- The existing canonical comparison preserves this nonvanishing in the
actual sphere tower's internal E₂ page. -/
theorem internal_hi_ne_zero (i : ℕ) : Sphere.Internal.hi H M i ≠ 0 := by
  rw [← comparison_hi H M i]
  exact fun h => hi_ne_zero H M i ((comparison H M 1 (2 ^ i)).map_eq_zero_iff.mp h)

end
end KIP126.Classical.Adams.MilnorCohomology
