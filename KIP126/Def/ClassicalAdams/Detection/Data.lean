module

public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs
public import KIP126.Def.SpectralSequence.Convergence.Data

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

def homotopy (X : C) (n : ℤ) : ModuleCat.{v} ℤ := ModuleCat.of ℤ (HomotopyGroup n X)
def filtrationSubmodule (X : C) (s n : ℤ) : Submodule ℤ (homotopy X n) :=
  LinearMap.range (inducedMap (adamsTowerMap unit X 0 s.toNat (Nat.zero_le _)) n).toIntLinearMap
end
end KIP126.Classical.Adams.TowerDetection
