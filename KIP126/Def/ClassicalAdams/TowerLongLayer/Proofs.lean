module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Data
public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Proofs
public import KIP126.Def.ClassicalAdams.TowerDifferential.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The actual boundary of a long-layer representative lifts the connecting
image of its projection to the original first-page module. -/
theorem adamsLongLayerK_lift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : HomotopyGroup (t - s) (adamsLongLayer unit X r hr s)) :
    adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega)
        (adamsLongLayerK unit X r hr s t z) =
      adamsK unit X s t (adamsLongLayerToE1 unit X r hr s t z) :=
  (cofiberFactorizationMap_connecting
    (adamsTowerMapAt unit X s (s + r) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))
    (adamsTowerMapAt_comp unit X s (s + 1) (s + r) (by omega) (by omega))
    (t - s) z).symm

/-- Every `r`-cycle, not just a zero-connecting-image representative, comes
from the cofiber of the actual `r`-step tower map, and conversely. -/
theorem adamsCycles_mem_iff_longLayer (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsE1 unit X s t) :
    x ∈ adamsCycles unit X r hr s t ↔
      ∃ z : HomotopyGroup (t - s) (adamsLongLayer unit X r hr s),
        adamsLongLayerToE1 unit X r hr s t z = x :=
  (cofiberFactorizationMap_image_iff
    (adamsTowerMapAt unit X s (s + r) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))
    (adamsTowerMapAt_comp unit X s (s + 1) (s + r) (by omega) (by omega))
    (t - s) x).symm

end
end KIP126.Classical.Adams
