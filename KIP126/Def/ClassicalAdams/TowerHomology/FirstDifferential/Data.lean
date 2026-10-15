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

/-- The representative first differential in homology degree `n`, before
reindexing to the Adams bidegrees. Both maps come from the actual tower. -/
def adamsHomologyD1 (X : C) (n : ℤ) :
    Mod2Homology H n X →ₗ[ℤ] Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  (inducedMap (adamsUnit H.unit (fiber (adamsUnit H.unit X))) (n - 1)).toIntLinearMap.comp
    (adamsResolutionBoundary H.unit X 0 n).toIntLinearMap

end

end KIP126.Classical.Adams
