module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Bijective.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The canonical finite top-weight equivalence. Its forward map is the
original top-class map, with its canonical integer-module structures. -/
def finiteTopEquiv (q : ℕ) (p : ℤ × ℤ) :
    cycles H X q p ≃ₗ[ℤ] CycleQuotient H X (q - p.2 + p.2) (1 + p.2 - p.2) p :=
  LinearEquiv.ofBijective (finiteTopClass H X q p) (finiteTopClass_bijective H X q p)

/-- The canonical permanent top-weight equivalence, retaining the actual
permanent representative label. -/
def permanentTopEquiv (p : ℤ × ℤ) :
    permanentCycles H X p ≃ₗ[ℤ] PermanentQuotient H X (1 + p.2 - p.2) p :=
  LinearEquiv.ofBijective (permanentTopClass H X p) (permanentTopClass_bijective H X p)

end
end KIP126.Classical.Adams.PageRepresentatives
