module

public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Data

@[expose] public section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD : FilteredComplex C}

/-- Restrict both representatives using the same filtered chain map. -/
noncomputable def representativesMap (f : Morphism FC GD) (T : C) (r s k : ℤ) :
    Representatives FC T r s k →+ Representatives GD T r s k where
  toFun z := (z.1 ≫ (f.preserves s k).choose,
    z.2 ≫ (f.preserves (s + r) (k - 1)).choose)
  map_zero' := by simp
  map_add' _ _ := by simp [Preadditive.add_comp]

/-- Restriction on the labels and the actual ambient discrepancy. -/
noncomputable def equationsMap (f : Morphism FC GD) (T : C) (r s k : ℤ) :
    Equations FC T r s k →+ Equations GD T r s k where
  toFun z := (z.1 ≫ f.associatedGradedMap s k,
    z.2.1 ≫ f.associatedGradedMap (s + r) (k - 1), z.2.2 ≫ f.map.f (k - 1))
  map_zero' := by simp
  map_add' _ _ := by simp [Preadditive.add_comp]

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
