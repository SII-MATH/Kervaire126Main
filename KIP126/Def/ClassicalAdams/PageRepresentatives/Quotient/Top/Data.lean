module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Window.Data

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Algebra

universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The canonical top-weight class of a cycle, retaining its actual E₂ label. -/
def finiteTopClass (q : ℕ) (p : ℤ × ℤ) :
    cycles H X q p →ₗ[ℤ] CycleQuotient H X (q - p.2 + p.2) (1 + p.2 - p.2) p :=
  ((NestedQuotient.projection (cycles H X (q - p.2 + p.2) p)
    (boundaries H X (1 + p.2 - p.2) p)).comp
    (Submodule.inclusion (show cycles H X q p ≤ cycles H X (q - p.2 + p.2) p by
      rw [sub_add_cancel]))).toAddMonoidHom.toIntLinearMap

/-- The same permanent representative in the ν top-weight quotient. -/
def permanentTopClass (p : ℤ × ℤ) :
    permanentCycles H X p →ₗ[ℤ] PermanentQuotient H X (1 + p.2 - p.2) p :=
  (NestedQuotient.projection (permanentCycles H X p)
    (boundaries H X (1 + p.2 - p.2) p)).toAddMonoidHom.toIntLinearMap

end
end KIP126.Classical.Adams.PageRepresentatives
