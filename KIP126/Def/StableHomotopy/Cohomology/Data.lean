module

public import KIP126.Def.StableHomotopy.Context.Data
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Explicit mod-2 cohomology and homology data

The historical module selected an Eilenberg--Mac Lane spectrum, a Steenrod
algebra, and a universal-coefficient equivalence with global axioms.  This
port keeps those choices in records.  The representable mod-2 groups and
their functorial maps are then ordinary definitions from the stable category.
-/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- An explicit mod-2 Eilenberg--Mac Lane input. -/
structure Mod2EilenbergMacLane where
  HF2 : C
  pi0Equiv : HomotopyGroup 0 HF2 ≃+ ZMod 2
  /-- Vanishing means the group has only its zero element, not that it is empty. -/
  homotopy_vanishes : ∀ (n : ℤ), n ≠ 0 → Subsingleton (HomotopyGroup n HF2)

/-- The unit map representing `1 ∈ π₀(H𝔽₂) = 𝔽₂`. -/
def Mod2EilenbergMacLane.unit (H : Mod2EilenbergMacLane (C := C)) :
    SphereSpectrum ⟶ H.HF2 :=
  (shiftFunctorZero C ℤ).inv.app SphereSpectrum ≫ H.pi0Equiv.symm 1

/-- The n-th mod-2 homology group, represented by `HF2 ⊗ X`. -/
abbrev Mod2Homology (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) (X : C) : Type v :=
  HomotopyGroup n (H.HF2 ⊗ X)

/-- Pushforward in mod-2 homology. -/
def Mod2Homology.pushforward (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    Mod2Homology H n X →+ Mod2Homology H n Y :=
  inducedMap (H.HF2 ◁ f) n

end KIP126.StableHomotopy.Cohomology
