module

public import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Proofs
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

/-! The actual category of enriched operadic algebras and its forgetful
functors, including the unit arrow. Category composition is the composition
of the underlying model category, not a further choice. -/

namespace KIP126.HigherAlgebra.Operad.EnrichedAlgebra

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]
  (P : Presentation M) (hP : TensorLaws P) (O : TopologicalOperad.{w})

instance : Category (EnrichedAlgebra P hP O) where
  Hom := Hom
  id A := ⟨𝟙 A.carrier, identity_commutes A⟩
  comp f g := ⟨f.hom ≫ g.hom, composition_commutes f g⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- Forget the action, retaining the exact object and morphism. -/
def forget : EnrichedAlgebra P hP O ⥤ M where
  obj A := A.carrier
  map f := f.hom

/-- Forget the action while retaining its actual nullary unit. -/
def unitForget (o : O.Op empty) : EnrichedAlgebra P hP O ⥤ Under (𝟙_ M) where
  obj A := Under.mk (unit o A)
  map f := Under.homMk f.hom (unit_naturality o f)
  map_id _ := Under.UnderMorphism.ext rfl
  map_comp _ _ := Under.UnderMorphism.ext rfl

end KIP126.HigherAlgebra.Operad.EnrichedAlgebra
