module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Data

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD GE : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

/-- The action on each nonempty fiber is respected by restriction. -/
theorem restrict_translate (f : Morphism FC GD) (g : differences FC T r s k)
    (a : Fiber FC r s k x y) :
    restrict f (translate g a) =
      translate (restrictDifferences f T r s k g) (restrict f a) := by
  apply Subtype.ext
  exact map_add (representativesMap f T r s k) g.val a.val

theorem restrictDifferences_id (g : differences FC T r s k) :
    restrictDifferences (Morphism.id FC) T r s k g = g := by
  apply Subtype.ext
  exact representativesMap_id T r s k g.val

theorem restrictDifferences_comp (f : Morphism FC GD) (g : Morphism GD GE)
    (a : differences FC T r s k) :
    restrictDifferences (Morphism.comp f g) T r s k a =
      restrictDifferences g T r s k (restrictDifferences f T r s k a) := by
  apply Subtype.ext
  exact representativesMap_comp f g T r s k a.val

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
