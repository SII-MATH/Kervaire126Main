module

import all KIP126.SpectralSequence.FilteredComplex.Solutions.Obstruction.Data

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

/-- Exactness at the actual earlier solution fiber, with no nonemptiness
assumption on the later fiber. This is not yet a crossing/loss certificate. -/
theorem obstruction_eq_zero_iff (f : Morphism FC GD)
    (a : Fiber GD r s k (x ≫ f.associatedGradedMap s k)
      (y ≫ f.associatedGradedMap (s + r) (k - 1))) :
    obstruction f x y a = 0 ↔ ∃ b : Fiber FC r s k x y, restrict f b = a := by
  change QuotientAddGroup.mk ((x, y, 0), a.val) = 0 ↔ _
  erw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    have he : equation FC T r s k z = (x, y, 0) := congrArg Prod.fst hz
    have hm : representativesMap f T r s k z = a.val := congrArg Prod.snd hz
    exact ⟨⟨z, he⟩, Subtype.ext hm⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.val, Prod.ext b.property (congrArg Subtype.val hb)⟩

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
