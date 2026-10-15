module

public import KIP126.Def.Algebra.GradedComodule.Shift.Data
public import KIP126.Def.Algebra.GradedComodule.Structure.Data
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

@[expose] public section

/-!
Derived Ext in the actual abelian category of graded right comodules.
The derived category is Mathlib's localization at quasi-isomorphisms. The
larger standard Ext universe avoids requiring an injective resolution merely
to define these groups. No cobar quotient is renamed as Ext here.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K]

/-- The standard derived-category universe is sufficient for these comodules. -/
instance hasExt (C : Comon (GrVect K)) : HasExt.{u + 1} (RightComodule C) :=
  HasExt.standard _

/-- Internal degree `t` shifts the first variable; `s` is the independent
nonnegative derived degree. The shift is the actual tensor construction. -/
abbrev BigradedExt (C : Comon (GrVect K)) (M N : RightComodule C)
    (s : ℕ) (t : ℤ) : Type (u + 1) :=
  Abelian.Ext.{u + 1} ((internalShift K C t).obj M) N s

/-- Sphere coefficients in the right-comodule convention are
`Ext^s(k[t], k)`. The source and target use the same coaugmentation. -/
abbrev CoefficientExt {C : Comon (GrVect K)} (η : Coaugmentation C)
    (s : ℕ) (t : ℤ) : Type (u + 1) :=
  Abelian.Ext.{u + 1} (trivialAt K η t) (trivialAt K η 0) s

/-- The actual degree-zero Ext class of the identity on the trivial comodule. -/
noncomputable def coefficientUnit {C : Comon (GrVect K)} (η : Coaugmentation C) :
    CoefficientExt η 0 0 :=
  Abelian.Ext.mk₀ (𝟙 (trivialAt K η 0))

end KIP126.Algebra.GradedComodule
