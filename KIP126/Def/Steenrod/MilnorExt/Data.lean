module

public import KIP126.Def.Algebra.GradedComodule.Ext.Data
public import KIP126.Def.Steenrod.MilnorCoalgebra.Data

@[expose] public section

/-!
The theory-side sphere Ext groups for the fixed Milnor coproduct.
They are genuine derived Ext of its graded right-comodule category. Relating
them to normalized cobar cohomology, and then to left Steenrod-module Ext,
requires separate comparison statements; neither is implicit in this alias.
-/

namespace KIP126.Steenrod.Milnor.Ext

open CategoryTheory KIP126.Algebra
open KIP126.Algebra

/-- Right comodules over the actual polynomial Milnor coalgebra. -/
abbrev RightComodule := GradedComodule.RightComodule Coalgebra.dualSteenrod

/-- The fixed trivial comodule in integer degree `t`. -/
noncomputable def trivialAt (t : ℤ) : RightComodule :=
  GradedComodule.trivialAt F2 Coalgebra.coaugmentation t

/-- Derived degree `s` and internal degree `t`, with the right-comodule
convention `Ext^s(k[t], k)`. Negative internal degrees are not coerced to zero. -/
abbrev SphereExt (s : ℕ) (t : ℤ) : Type 1 :=
  GradedComodule.CoefficientExt Coalgebra.coaugmentation s t

/-- The identity class in the fixed `(0,0)` Ext group. -/
noncomputable def unit : SphereExt 0 0 :=
  GradedComodule.coefficientUnit Coalgebra.coaugmentation

end KIP126.Steenrod.Milnor.Ext
