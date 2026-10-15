module

public import KIP126.Def.ClassicalAdams.TowerPages.Proofs
public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The actual cofiber of the composite of `r` tower steps. Its homotopy
classes will represent the existing `r`-cycles, not a replacement sequence. -/
abbrev adamsLongLayer (r : ℕ) (hr : 1 ≤ r) (s : ℤ) : C :=
  HasFunctorialCofiber.cofib (adamsTowerMapAt unit X s (s + r) (by omega))

/-- Projection from the long layer to the original one-step layer, through
the factorization `T_(s+r) → T_(s+1) → T_s`. -/
def adamsLongLayerProjection (r : ℕ) (hr : 1 ≤ r) (s : ℤ) :
    adamsLongLayer unit X r hr s ⟶ adamsLayerAt unit X s :=
  cofiberFactorizationMap
    (adamsTowerMapAt unit X s (s + r) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + r) (by omega))
    (adamsTowerMapAt_comp unit X s (s + 1) (s + r) (by omega) (by omega))

/-- The represented projection to the existing first-page ambient module. -/
def adamsLongLayerToE1 (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X r hr s) →ₗ[ℤ]
      adamsE1 unit X s t :=
  (inducedMap (adamsLongLayerProjection unit X r hr s) (t - s)).toIntLinearMap

/-- The connecting homomorphism of the long cofiber, with values directly
in `T_(s+r)`. It will supply a lift for the actual page differential. -/
def adamsLongLayerK (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X r hr s) →ₗ[ℤ]
      HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)) :=
  (connectingHomomorphism (HoCofiberSequence.ofMorphism
    (adamsTowerMapAt unit X s (s + r) (by omega))) (t - s)).toIntLinearMap

end
end KIP126.Classical.Adams
