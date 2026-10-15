module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.AdjoinPoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

instance adjoinPoint_compactSpace (A : TopCat.{u}) [CompactSpace A] :
    CompactSpace (adjoinPoint A) := inferInstanceAs (CompactSpace (A ⊕ PUnit))

instance adjoinPoint_t2Space (A : TopCat.{u}) [T2Space A] :
    T2Space (adjoinPoint A) := inferInstanceAs (T2Space (A ⊕ PUnit))

theorem adjoinPointMap_injective {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : Function.Injective f) : Function.Injective (adjoinPointMap f).map :=
  Sum.map_injective.mpr ⟨hf,Function.injective_id⟩

theorem adjoinPointEquiv_precomp {A B : TopCat.{u}} (f : A ⟶ B)
    {X : BasedSpace.{u}} (g : adjoinPoint B ⟶ X) :
    adjoinPointEquiv A X (adjoinPointMap f ≫ g) =
      (adjoinPointEquiv B X g).comp f.hom := rfl

theorem adjoinPointEquiv_postcomp (A : TopCat.{u})
    {X Y : BasedSpace.{u}} (f : adjoinPoint A ⟶ X) (g : X ⟶ Y) :
    adjoinPointEquiv A Y (f ≫ g) = g.map.comp (adjoinPointEquiv A X f) := rfl

end KIP126.StableHomotopy.Spectra.BasedSpace
