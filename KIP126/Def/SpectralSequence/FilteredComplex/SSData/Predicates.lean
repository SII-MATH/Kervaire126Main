module

public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Data
public import KIP126.Def.Algebra.Filtration.Predicates

@[expose] public section

/-!
# Boundedness and cycle-boundary predicates for filtered complexes
-/

namespace KIP126.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Historical two-sided boundedness record, with its original field names. -/
structure IsBounded (FC : FilteredComplex C) where
  /-- Degreewise lower bound. -/
  lo : ℤ → ℤ
  /-- Degreewise upper bound. -/
  hi : ℤ → ℤ
  /-- The bounds occur in the expected order. -/
  lo_le_hi : ∀ k, lo k ≤ hi k
  /-- Low filtration levels are the whole object. -/
  boundedBelow : ∀ k s, s ≤ lo k → FC.fil s k = ⊤
  /-- High filtration levels are zero. -/
  boundedAbove : ∀ k s, hi k ≤ s → FC.fil s k = ⊥

/-- A filtered representative `xl` lifts the associated-graded element `x`. -/
def IsLift (FC : FilteredComplex C) {T : C} (s k : ℤ)
    (xl : T ⟶ Subobject.underlying.obj (FC.fil s k))
    (x : T ⟶ FC.assocGraded s k) : Prop :=
  xl ≫ FC.filToAssocGraded s k = x

/-- A strict filtered-lift relation between associated-graded representatives. -/
def RepresentativeRelation (FC : FilteredComplex C)
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C}
    (x : T ⟶ FC.filtration.associatedGraded s k)
    (y : T ⟶ FC.filtration.associatedGraded (s + r) (k - 1)) : Prop :=
  ∃ (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))),
    xl ≫ FC.filtration.toAssociatedGraded s k = x ∧
    yl ≫ FC.filtration.toAssociatedGraded (s + r) (k - 1) = y ∧
    xl ≫ FC.filDiff s k =
      yl ≫ FC.filtration.inclusion (by omega) (k - 1)

end FilteredComplex

end KIP126.SpectralSequence
