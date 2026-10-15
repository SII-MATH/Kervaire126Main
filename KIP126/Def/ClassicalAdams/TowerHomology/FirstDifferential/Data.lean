module

public import KIP126.Def.ClassicalAdams.TowerHomology.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- The original unit fiber triangle, before smashing with `H`. -/
def adamsResolutionSequence (X : C) : HoCofiberSequence (C := C) where
  X := fiber (adamsUnit H.unit X)
  Y := X
  Z := H.HF2 ⊗ X
  f := fiberι (adamsUnit H.unit X)
  g := adamsUnit H.unit X
  h := adamsResolutionConnecting H.unit X 0
  distinguished := adamsResolutionTriangle_distinguished H.unit X 0

end

end KIP126.Classical.Adams
