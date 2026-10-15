module

public import KIP126.Def.StableHomotopy.Spectra.Generators
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory

universe u

/-- The actual one-point space used to express specified basepoints. -/
abbrev pointSpace : TopCat.{u} := TopCat.of PUnit.{u+1}

/-- Regard a specified basepoint as an actual map from the one-point space. -/
def toUnder : BasedSpace.{u} ⥤ Under pointSpace where
  obj X := Under.mk (TopCat.ofHom (ContinuousMap.const _ X.point))
  map f := Under.homMk (TopCat.ofHom f.map) (by
    apply ConcreteCategory.hom_ext
    intro x
    exact f.point)
  map_id X := by apply Under.UnderMorphism.ext; rfl
  map_comp f g := by apply Under.UnderMorphism.ext; rfl

/-- Recover the specified point from the actual point inclusion. -/
def fromUnder : Under pointSpace.{u} ⥤ BasedSpace.{u} where
  obj X := ⟨X.right, X.hom PUnit.unit⟩
  map f :=
    { map := f.right.hom
      point := congrArg (fun k => k PUnit.unit) (Under.w f) }
  map_id X := by apply Hom.ext; rfl
  map_comp f g := by apply Hom.ext; rfl

/-- The existing based-space category is equivalent to the actual
undercategory of the one-point topological space. -/
def underEquivalence : BasedSpace.{u} ≌ Under pointSpace where
  functor := toUnder
  inverse := fromUnder
  unitIso := NatIso.ofComponents (fun X => Iso.refl X)
  counitIso := NatIso.ofComponents
    (fun X => Under.isoMk (Iso.refl X.right) (by
      apply ConcreteCategory.hom_ext
      intro x
      cases x
      rfl))

/-- Forget the specified point, retaining the actual space and continuous map. -/
def forgetToTop : BasedSpace.{u} ⥤ TopCat.{u} := toUnder ⋙ Under.forget pointSpace

end KIP126.StableHomotopy.Spectra.BasedSpace
