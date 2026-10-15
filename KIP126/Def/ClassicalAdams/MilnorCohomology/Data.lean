module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Complex.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Hi.Proofs
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Normalized Milnor cobar cohomology

This is the actual F₂-module `ker d / im d`, with the degree-zero incoming
image defined to be zero. The inclusion of boundaries into cycles uses the
proved square-zero consequence of the same `H` and `M`; no new hypothesis or
axiom is supplied. Its identification with the internal Adams E₂ page or
with Ext is not part of this construction.
-/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The actual incoming boundaries, included into the cycle module using the
square-zero theorem for this Milnor cooperation comparison. -/
def boundariesInCycles (s t : ℕ) : Submodule F2 (cycles s t) :=
  LinearMap.range (Submodule.inclusion (boundaries_le_cycles H M s t))

/-- Normalized cobar cohomology as an F₂-module quotient. -/
abbrev Cohomology (s t : ℕ) := (cycles s t) ⧸ boundariesInCycles H M s t

/-- The canonical linear map from actual cycles to their cohomology classes. -/
def classOf (s t : ℕ) : cycles s t →ₗ[F2] Cohomology H M s t :=
  (boundariesInCycles H M s t).mkQ

/-- The class of a specified closed normalized cochain. -/
def ofCocycle {s t : ℕ} (x : cochains s t) (hx : differential s t x = 0) :
    Cohomology H M s t :=
  classOf H M s t ⟨x, hx⟩

/-- The class represented by `[ξ₁^(2^i)]`, not an independently chosen element. -/
def hi (i : ℕ) : Cohomology H M 1 (2 ^ i) :=
  ofCocycle H M (hiCochain i) (hiCochain_isCycle i)

/-- The class of the already defined concatenation square. Descent of the
full cup product to a cohomology ring is a separate construction. -/
def hiSquare (i : ℕ) : Cohomology H M 2 (2 ^ (i + 1)) :=
  ofCocycle H M (hiSquareCochain i) (hiSquareCochain_isCycle i)

end
end KIP126.Classical.Adams.MilnorCohomology
