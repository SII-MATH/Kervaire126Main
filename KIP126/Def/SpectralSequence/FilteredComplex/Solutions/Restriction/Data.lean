module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Affine.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Morphism.Proofs

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD : FilteredComplex C} {T : C} {r s k : ℤ}

/-- Restriction of a solution is induced by the actual filtered chain map. -/
noncomputable def restrict (f : Morphism FC GD)
    {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (a : Fiber FC r s k x y) :
    Fiber GD r s k (x ≫ f.associatedGradedMap s k)
      (y ≫ f.associatedGradedMap (s + r) (k - 1)) :=
  ⟨representativesMap f T r s k a.val, by
    rw [equation_natural, a.property]
    simp [equationsMap]⟩

/-- The induced homomorphism on the actual groups of differences. -/
noncomputable def restrictDifferences (f : Morphism FC GD) (T : C) (r s k : ℤ) :
    differences FC T r s k →+ differences GD T r s k where
  toFun g := ⟨representativesMap f T r s k g.val, by
    change equation GD T r s k _ = 0
    rw [equation_natural, show equation FC T r s k g.val = 0 from g.property,
      map_zero]⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' a b := by apply Subtype.ext; exact map_add _ a.val b.val

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
