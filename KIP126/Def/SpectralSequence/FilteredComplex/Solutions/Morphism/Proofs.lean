module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Morphism.Data

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD GE : FilteredComplex C}

/-- The actual representative equations commute with every filtered chain map. -/
theorem equation_natural (f : Morphism FC GD) (T : C) (r s k : ℤ)
    (z : Representatives FC T r s k) :
    equation GD T r s k (representativesMap f T r s k z) =
      equationsMap f T r s k (equation FC T r s k z) := by
  have hs := Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap
    f.toFilteredMorphism s k
  have ht := Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap
    f.toFilteredMorphism (s + r) (k - 1)
  apply Prod.ext
  · change (z.1 ≫ (f.preserves s k).choose) ≫ GD.filToAssocGraded s k =
      (z.1 ≫ FC.filToAssocGraded s k) ≫ f.associatedGradedMap s k
    simpa only [Category.assoc, filToAssocGraded, Morphism.associatedGradedMap,
      Morphism.toFilteredMorphism] using congrArg (fun a => z.1 ≫ a) hs.symm
  apply Prod.ext
  · change (z.2 ≫ (f.preserves (s + r) (k - 1)).choose) ≫
        GD.filToAssocGraded (s + r) (k - 1) =
      (z.2 ≫ FC.filToAssocGraded (s + r) (k - 1)) ≫
        f.associatedGradedMap (s + r) (k - 1)
    simpa only [Category.assoc, filToAssocGraded, Morphism.associatedGradedMap,
      Morphism.toFilteredMorphism] using congrArg (fun a => z.2 ≫ a) ht.symm
  · change (z.1 ≫ (f.preserves s k).choose) ≫ (GD.fil s k).arrow ≫ GD.d k -
        (z.2 ≫ (f.preserves (s + r) (k - 1)).choose) ≫
          (GD.fil (s + r) (k - 1)).arrow =
      (z.1 ≫ (FC.fil s k).arrow ≫ FC.d k -
        z.2 ≫ (FC.fil (s + r) (k - 1)).arrow) ≫ f.map.f (k - 1)
    have hs' := congrArg (fun a => a ≫ GD.d k) (f.preserves s k).choose_spec
    simp only [Category.assoc] at hs'
    simp only [Category.assoc, Preadditive.sub_comp]
    rw [hs', (f.preserves (s + r) (k - 1)).choose_spec]
    simp only [d]
    rw [f.map.comm]

theorem representativesMap_id (T : C) (r s k : ℤ)
    (z : Representatives FC T r s k) :
    representativesMap (Morphism.id FC) T r s k z = z := by
  simp [representativesMap, Morphism.id_preserves_eq]

theorem representativesMap_comp (f : Morphism FC GD) (g : Morphism GD GE)
    (T : C) (r s k : ℤ) (z : Representatives FC T r s k) :
    representativesMap (Morphism.comp f g) T r s k z =
      representativesMap g T r s k (representativesMap f T r s k z) := by
  simp [representativesMap, Morphism.comp_preserves_eq, Category.assoc]

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
