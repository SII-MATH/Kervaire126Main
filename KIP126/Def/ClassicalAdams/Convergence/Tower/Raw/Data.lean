module

public import KIP126.Def.ClassicalAdams.Tower.Data
public import KIP126.Def.Algebra.Filtration.Data
public import Mathlib.Algebra.Category.ModuleCat.Subobject

@[expose] public section

/-! The actual Adams filtration on the homotopy groups of the specified
spectrum. Every level is the image of the existing tower map to that spectrum. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The homotopy groups of this spectrum, with their canonical integer module structure. -/
def towerAbutment : GradedObject ℤ (ModuleCat.{v} ℤ) :=
  fun n => ModuleCat.of ℤ (HomotopyGroup n X)

/-- The actual map from filtration level `s` to the original spectrum.
Nonpositive levels use the existing constant extension of the Adams tower. -/
def adamsTowerToSpectrum (s : ℤ) : adamsTowerAt unit X s ⟶ X :=
  adamsTowerMap unit X 0 s.toNat (Nat.zero_le _)

/-- The actual image on homotopy, with no chosen filtration or abutment. -/
def adamsHomotopyFiltrationSubmodule (s n : ℤ) :
    Submodule ℤ (HomotopyGroup n X) :=
  LinearMap.range (inducedMap (adamsTowerToSpectrum unit X s) n).toIntLinearMap

end KIP126.Classical.Adams
