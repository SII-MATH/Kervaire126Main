module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

/-!
# Filtered graded objects

This file supplies the part of the shared KIP126 that is not already a Mathlib
object: decreasing filtrations by subobjects of a graded object, their
associated graded pieces, and filtration-preserving maps.  Filtrations and
filtered maps work in an arbitrary category; quotient-based associated graded
pieces work in an abelian category.  Neither layer assumes a field or an
elementwise presentation.
-/

namespace KIP126.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A decreasing filtration of a graded object.  `F s i` denotes the
subobject $F^s A_i$, and `decreasing` says $F^{s+1} A_i \le F^s A_i$. -/
structure Filtration {ι : Type w} (A : CategoryTheory.GradedObject ι C) where
  /-- The filtration subobject at a filtration level and grading index. -/
  F : ℤ → (i : ι) → Subobject (A i)
  /-- The filtration is decreasing. -/
  decreasing : ∀ (s : ℤ) (i : ι), F (s + 1) i ≤ F s i

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-! ### Maps between arbitrary filtration levels

The successor inequality in `Filtration.decreasing` is the compact datum from
which all of the maps in the filtration diagram are obtained.  Keeping this
construction here (rather than re-proving it in the filtered-complex layer)
also fixes the variance convention once and for all: for `t ≤ s`, the
decreasing filtration has an inclusion `F s ↪ F t`.
-/

/-- Monotonicity of a decreasing filtration at arbitrary integer levels. -/
lemma le_of_le (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.F s i ≤ F.F t i := by
  induction s, h using Int.leInduction with
  | base => exact le_rfl
  | succ s _ ih =>
      exact (F.decreasing s i).trans ih

/-- The canonical inclusion `Fˢ Aᵢ ⟶ Fᵗ Aᵢ` when `t ≤ s`. -/
noncomputable def inclusion (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (F.F t i) :=
  Subobject.ofLE (F.F s i) (F.F t i) (F.le_of_le h i)

@[simp]
lemma inclusion_arrow (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.inclusion h i ≫ (F.F t i).arrow = (F.F s i).arrow :=
  Subobject.ofLE_arrow _

@[reassoc (attr := simp)]
lemma inclusion_comp (F : Filtration A) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    F.inclusion hst i ≫ F.inclusion hrs i = F.inclusion (hrs.trans hst) i := by
  simp [inclusion]

/-- The associated graded piece
$\operatorname{gr}^s_F A_i = F^s A_i/F^{s+1} A_i$. -/
noncomputable def associatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) : C :=
  cokernel (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-- The quotient map from a filtration level to its associated graded piece. -/
noncomputable def toAssociatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ F.associatedGraded s i :=
  cokernel.π (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-! ### Index transport for associated graded pieces

The associated graded object is indexed by a product, so equal reindexings
must be transported explicitly when a construction changes the presentation
of a bidegree.  This is the canonical replacement for the corresponding
filtration comparison used in the convergence construction. -/

end Filtration



end KIP126.Algebra
