module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import KIP126.Def.ClassicalAdams.TowerPages.Data

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

def adamsLayerInduced {X Y : C} (f : X ⟶ Y) (s : ℤ) :
    adamsLayerAt unit X s ⟶ adamsLayerAt unit Y s :=
  HasFunctorialCofiber.cofibMap
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit Y s (s + 1) (by omega))
    (adamsTowerInduced unit f (s + 1).toNat) (adamsTowerInduced unit f s.toNat)
    (adamsTowerInduced_mapAt unit f s (s + 1) (by omega))

def adamsE1Induced {X Y : C} (f : X ⟶ Y) (s t : ℤ) :
    adamsE1 unit X s t →ₗ[ℤ] adamsE1 unit Y s t :=
  (inducedMap (adamsLayerInduced unit f s) (t - s)).toIntLinearMap

def adamsTowerHomInduced {X Y : C} (f : X ⟶ Y) (n s : ℤ) :
    HomotopyGroup n (adamsTowerAt unit X s) →ₗ[ℤ]
      HomotopyGroup n (adamsTowerAt unit Y s) :=
  (inducedMap (adamsTowerInduced unit f s.toNat) n).toIntLinearMap

end KIP126.Classical.Adams
