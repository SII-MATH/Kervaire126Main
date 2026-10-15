module

public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Data
public import KIP126.Def.Algebra.Filtration.Data

@[expose] public section

/-!
# Boundedness and cycle-boundary predicates for filtered complexes
-/

namespace KIP126.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- A filtered representative `xl` lifts the associated-graded element `x`. -/
def IsLift (FC : FilteredComplex C) {T : C} (s k : ℤ)
    (xl : T ⟶ Subobject.underlying.obj (FC.fil s k))
    (x : T ⟶ FC.assocGraded s k) : Prop :=
  xl ≫ FC.filToAssocGraded s k = x

end FilteredComplex

end KIP126.SpectralSequence
