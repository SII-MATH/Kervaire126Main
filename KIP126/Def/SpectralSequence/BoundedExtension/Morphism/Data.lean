module

public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs

@[expose] public section

/-!
# Filtration-preserving chain maps and associated-graded maps

`FilteredComplexMorphism` denotes a filtration-preserving chain map.
Its maps on associated-graded objects are induced by the same chain map.
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtration-preserving chain map. -/
abbrev FilteredComplexMorphism (FC₁ FC₂ : FilteredComplex C) :=
  FilteredComplex.Morphism FC₁ FC₂

namespace FilteredComplexMorphism

/-- The map in each chain degree. -/
@[reducible] def f {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (k : ℤ) :
    FC₁.A k ⟶ FC₂.A k :=
  g.map.f k

/-- The map induced on an associated-graded piece. -/
noncomputable def assocGradedMap
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂)
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  g.associatedGradedMap s k

end FilteredComplexMorphism

end KIP126.SpectralSequence
