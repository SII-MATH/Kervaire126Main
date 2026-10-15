module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- The actual map between the chosen fibers induced by a commuting square. -/
def fiberMap {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) : fiber f ⟶ fiber g :=
  (HasFunctorialCofiber.cofibMap f g a b h)⟦(-1 : ℤ)⟧'

/-- A spectrum map induces maps at every stage of its constructed Adams tower.
These are not an independently supplied family of maps. No identity/composition
law for the chosen cofiber-map operation is assumed here. -/
def adamsTowerInduced {X Y : C} (f : X ⟶ Y) :
    (s : ℕ) → (adamsTower unit X s ⟶ adamsTower unit Y s)
  | 0 => f
  | s + 1 => fiberMap (adamsUnit unit (adamsTower unit X s))
      (adamsUnit unit (adamsTower unit Y s))
      (adamsTowerInduced f s) (H ◁ adamsTowerInduced f s)
      (adamsUnit_naturality unit (adamsTowerInduced f s))

end KIP126.Classical.Adams
