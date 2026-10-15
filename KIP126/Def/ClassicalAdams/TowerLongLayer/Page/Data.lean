module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The long-layer projection corestricted to the actual cycle module. -/
def adamsLongLayerToCycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X r hr s) →ₗ[ℤ]
      adamsCycles unit X r hr s t :=
  (adamsLongLayerToE1 unit X r hr s t).codRestrict _
    (adamsLongLayerToE1_mem_cycles unit X r hr s t)

/-- Long-layer representatives map to the already constructed quotient page. -/
def adamsLongLayerToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X r hr s) →ₗ[ℤ]
      adamsPage unit X r hr s t :=
  (adamsCycleBoundaries unit X r hr s t).mkQ.comp
    (adamsLongLayerToCycles unit X r hr s t)

end
end KIP126.Classical.Adams
