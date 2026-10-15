module

public import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs
public import KIP126.Def.StableHomotopy.Context.Connecting.Proofs
import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

variable [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The last square of the map from the actual unit triangle to its smash
with `H`; its commutativity is derived from unit naturality and shift coherence. -/
theorem adamsResolutionSequence_unit_last_square (X : C) :
    adamsUnit H.unit (H.HF2 ⊗ X) ≫ (adamsHomologySequence H X).h =
      (adamsResolutionSequence H X).h ≫
        (adamsUnit H.unit (fiber (adamsUnit H.unit X)))⟦(1 : ℤ)⟧' := by
  change adamsUnit H.unit (H.HF2 ⊗ X) ≫
    H.HF2 ◁ adamsResolutionConnecting H.unit X 0 ≫
      ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (fiber (adamsUnit H.unit X)) = _
  rw [← Category.assoc, mod2AdamsUnit_naturality, Category.assoc]
  erw [mod2Unit_shift H (fiber (adamsUnit H.unit X)) 1]
  rfl

end

end KIP126.Classical.Adams
