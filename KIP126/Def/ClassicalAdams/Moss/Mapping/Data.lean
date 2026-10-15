module

public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs
public import Mathlib.Algebra.Category.ModuleCat.Subobject

@[expose] public section

/-!
Mapping Adams objects from the existing tower of the actual internal hom.
No mapping spectral sequence, tower stage or abutment is chosen independently.
Only the selected closed structure and tensor-left shift comparison are used;
the older universally quantified tensor-exactness record is not assumed.
-/

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- The mapping spectrum uses this very closed structure. -/
abbrev mappingObject (X Y : C) : C := (ihom X).obj Y

/-- The actual Adams sequence of the mapping spectrum. -/
abbrev mappingSequence (X Y : C) :=
  adamsTowerInternalSpectralSequence unit (mappingObject X Y)

/-- Its stages are the existing constructed Adams tower, not additional data. -/
abbrev mappingStage (X Y : C) (s : ℕ) := adamsTower unit (mappingObject X Y) s

/-- Its transition maps are the actual composites of tower successor maps. -/
abbrev mappingRestrict (X Y : C) (s t : ℕ) (hst : s ≤ t) :=
  adamsTowerMap unit (mappingObject X Y) s t hst

/-- Projection to the stage-zero mapping spectrum. -/
abbrev mappingToTarget (X Y : C) (s : ℕ) :
    mappingStage unit X Y s ⟶ mappingObject X Y :=
  mappingRestrict unit X Y 0 s (Nat.zero_le s)

/-- The abutment groups are the actual homotopy groups of that mapping spectrum. -/
def mappingAbutment (X Y : C) (n : ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (HomotopyGroup n (mappingObject X Y))

/-- Homotopy classes which lift to the specified stage of the actual tower. -/
def mappingFiltrationSubmodule (X Y : C) (s n : ℤ) :
    Submodule ℤ (mappingAbutment X Y n) :=
  LinearMap.range (inducedMap (mappingToTarget unit X Y s.toNat) n).toIntLinearMap

/-- The chosen tensor shift comparison identifies `X ⊗ Sⁿ` with `X[n]`. -/
def tensorSphereIso (X : C) [(tensorLeft X).CommShift ℤ] (n : ℤ) :
    X ⊗ Sphere n ≅ X⟦n⟧ :=
  ((tensorLeft X).commShiftIso n).app SphereSpectrum ≪≫
    (shiftFunctor C n).mapIso (ρ_ X)

/-- Actual closed adjunction, followed by the same selected shift comparison. -/
def mappingHomotopyEquiv (X Y : C) [(tensorLeft X).CommShift ℤ] (n : ℤ) :
    mappingAbutment X Y n ≃ (X⟦n⟧ ⟶ Y) :=
  ((ihom.adjunction X).homEquiv (Sphere n) Y).symm.trans
    (Iso.homCongr (tensorSphereIso X n) (Iso.refl Y))

end
end KIP126.Classical.Adams.Moss
