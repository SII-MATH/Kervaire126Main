module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Data
public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Lifting.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The lift can retain the specified connecting map as well as its
projection to the one-step layer. -/
theorem adamsLongLayerProjection_lift_of_boundary (r : ℕ) (hr : 1 ≤ r) (s : ℤ)
    {W : C} (x : W ⟶ adamsLayerAt unit X s)
    (y : W ⟶ (adamsTowerAt unit X (s + r))⟦(1 : ℤ)⟧)
    (hy : y ≫ (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))⟦(1 : ℤ)⟧' =
      x ≫ HasFunctorialCofiber.cofibδ (adamsTowerMapAt unit X s (s + 1) (by omega))) :
    ∃ z : W ⟶ adamsLongLayer unit X r hr s,
      z ≫ adamsLongLayerProjection unit X r hr s = x ∧
        z ≫ HasFunctorialCofiber.cofibδ (adamsTowerMapAt unit X s (s + r) (by omega)) = y :=
  cofiberFactorizationMap_lift_of_boundary
    (adamsTowerMapAt unit X s (s + r) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))
    (adamsTowerMapAt_comp unit X s (s + 1) (s + r) (by omega) (by omega)) x y hy

/-- Lift a spectrum map to an actual long layer exactly when its one-step
connecting map lifts through the suspended tower composite. -/
theorem adamsLongLayerProjection_lift_iff (r : ℕ) (hr : 1 ≤ r) (s : ℤ)
    {W : C} (x : W ⟶ adamsLayerAt unit X s) :
    (∃ z : W ⟶ adamsLongLayer unit X r hr s,
      z ≫ adamsLongLayerProjection unit X r hr s = x) ↔
      ∃ y : W ⟶ (adamsTowerAt unit X (s + r))⟦(1 : ℤ)⟧,
        y ≫ (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))⟦(1 : ℤ)⟧' =
          x ≫ HasFunctorialCofiber.cofibδ (adamsTowerMapAt unit X s (s + 1) (by omega)) :=
  cofiberFactorizationMap_lift_iff
    (adamsTowerMapAt unit X s (s + r) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))
    (adamsTowerMapAt_comp unit X s (s + 1) (s + r) (by omega) (by omega)) x

end KIP126.Classical.Adams
