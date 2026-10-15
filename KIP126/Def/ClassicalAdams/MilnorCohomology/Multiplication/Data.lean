module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Cycles.Proofs
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

/-! Cobar concatenation descended through the actual boundary quotients. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The bilinear cohomology product induced by the explicit cobar cup product.
Both quotient descents use proved Leibniz consequences. -/
def cup {s t s' t' : ℕ} :
    Cohomology H M s t →ₗ[F2] Cohomology H M s' t' →ₗ[F2]
      Cohomology H M (s + s') (t + t') :=
  (cycleCupClass H M s t s' t').liftQ₂
    (boundariesInCycles H M s t) (boundariesInCycles H M s' t')
    (boundaries_le_cycleCupClass_ker H M s t s' t')
    (boundaries_le_cycleCupClass_flip_ker H M s t s' t')

/-- Transport along equalities of the two grading indices. -/
def cohomologyReindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t') :
    Cohomology H M s t ≃ₗ[F2] Cohomology H M s' t' := by
  subst s'
  subst t'
  exact LinearEquiv.refl F2 _

end
end KIP126.Classical.Adams.MilnorCohomology
