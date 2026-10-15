module

public import KIP126.Def.ClassicalAdams.Tmf.Multiplication.Proofs
public import KIP126.Def.ClassicalAdams.TowerDifferential.Value.Data

@[expose] public section

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (T : Mon C)

/-- The actual unit `𝟙 → T` projected from stage zero into second cycles.
It is the same `MonObj.one` used by `Tmf.unit` and every Hurewicz map. -/
def unitSecondCycle : adamsCycles H.unit T.X 2 (by decide) 0 0 :=
  adamsJToCycles H.unit T.X 2 (by decide) 0 0
    ((shiftFunctorZero C ℤ).hom.app (𝟙_ C) ≫ (MonObj.one : 𝟙_ C ⟶ T.X))

variable [BraidedCategory C] (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ] [MonoidalPreadditive C]

/-- The prescribed first-layer product with its second-cycle membership
attached from the lower property layer. No representative or product is chosen. -/
def secondCycleMultiplication (s t s' t' : ℕ)
    (a : adamsCycles H.unit T.X 2 (by decide) s t)
    (b : adamsCycles H.unit T.X 2 (by decide) s' t') :
    adamsCycles H.unit T.X 2 (by decide)
      ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) :=
  ⟨firstMultiplication H T R s t s' t' a.val b.val,
    firstMultiplication_mem_secondCycles H T R s t s' t' a b⟩

end
end KIP126.Classical.Adams.Tmf
