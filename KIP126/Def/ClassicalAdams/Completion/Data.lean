module

public import KIP126.Def.ClassicalAdams.Tower.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The residual Adams tower obtained by the existing repeated fiber
construction on the same unit `𝟙 ⟶ H`. No page data enters this tower. -/
def adamsResidualSequence {H : C} (unit : 𝟙_ C ⟶ H) (X : C) :
    InverseSequence C where
  obj := adamsTower unit X
  step := adamsTowerStep unit X

end KIP126.Classical.Adams
