module

public import KIP126.Def.Synthetic.Context.LambdaPowers.Data

@[expose] public section

/-! Comparisons of the existing bigraded suspension functors, with explicit
degree equalities. No suspension functor or comparison is chosen afresh. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The specified addition comparison, transported to a named total degree. -/
noncomputable def biShiftAddIso (a b c : ℤ × ℤ) (h : a + b = c) :
    SyntheticCategory.biShift a ⋙ SyntheticCategory.biShift b ≅
      (SyntheticCategory.biShift c : Syn ⥤ Syn) :=
  SyntheticCategory.biShift_comp a b ≪≫
    eqToIso (congrArg SyntheticCategory.biShift h)

/-- The degree of the already defined `lambdaPow n`. -/
def lambdaDegree (n : ℕ) : ℤ × ℤ := (0, -(n : ℤ))

/-- The existing addition comparison on the λ axis, with no new choices. -/
noncomputable def lambdaShiftAddIso (i j k : ℕ) (h : i + j = k) :
    SyntheticCategory.biShift (lambdaDegree i) ⋙
        SyntheticCategory.biShift (lambdaDegree j) ≅
      (SyntheticCategory.biShift (lambdaDegree k) : Syn ⥤ Syn) :=
  biShiftAddIso (lambdaDegree i) (lambdaDegree j) (lambdaDegree k)
    (by subst k; ext <;> simp [lambdaDegree, Nat.cast_add, add_comm])

/-- The source map for restriction from the `j`th to the `i`th λ quotient.
It uses multiplication by the existing `lambdaPow (j-i)`, through the
specified addition comparison. Its commuting square is proved separately. -/
noncomputable def lambdaRestrictionSourceMap (i j : ℕ) (hij : i ≤ j) (X : Syn) :
    (SyntheticCategory.biShift (lambdaDegree j)).obj X ⟶
      (SyntheticCategory.biShift (lambdaDegree i)).obj X :=
  (lambdaShiftAddIso (j - i) i j (Nat.sub_add_cancel hij)).inv.app X ≫
    (SyntheticCategory.biShift (lambdaDegree i)).map (lambdaPow (j - i) X)

end KIP126.Synthetic.Context
