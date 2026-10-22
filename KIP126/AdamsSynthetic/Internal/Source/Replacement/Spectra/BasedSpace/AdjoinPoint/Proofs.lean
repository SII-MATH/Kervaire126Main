module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/AdjoinPoint/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

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

end KIP126.AdamsSynthetic.Source.BasedSpace
