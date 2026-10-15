module

public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Predicates
public import KIP126.Def.SpectralSequence.FilteredComplex.Data
public import KIP126.Def.SpectralSequence.Basic.Data
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

@[expose] public section

/-!
# Filtration, differential and associated-graded identities
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Compatibility of the associated-graded differential with the quotient maps. -/
theorem assocGradedDiff_compat (FC : FilteredComplex C) (s k : ℤ) :
    FC.filToAssocGraded s k ≫ FC.assocGradedDiff s k =
      FC.filDiff s k ≫ FC.filToAssocGraded s (k - 1) :=
  FC.toAssociatedGraded_comp_associatedGradedDifferential s k

end FilteredComplex

end KIP126.SpectralSequence
