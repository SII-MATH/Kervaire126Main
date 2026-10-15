module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Mod-two coefficients

The Adams constructions use the field `F₂ = ZMod 2` and its abelian
category of modules.
-/

namespace KIP126.Algebra

/-- The field of two elements. -/
abbrev F2 := ZMod 2

/-- The abelian category of vector spaces over the field of two elements. -/
abbrev F2ModuleCat := ModuleCat F2

end KIP126.Algebra
