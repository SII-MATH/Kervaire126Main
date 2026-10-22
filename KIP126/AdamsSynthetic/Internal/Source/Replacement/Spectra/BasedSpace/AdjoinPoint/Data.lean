module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/AdjoinPoint/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory

universe u

/-- Adjoin a disjoint specified point to the actual topological space. -/
def adjoinPoint (A : TopCat.{u}) : BasedSpace.{u} where
  space := TopCat.of (A ⊕ PUnit)
  point := Sum.inr PUnit.unit

/-- A continuous map acts on the original summand and fixes the adjoined point. -/
def adjoinPointMap {A B : TopCat.{u}} (f : A ⟶ B) : adjoinPoint A ⟶ adjoinPoint B where
  map := ⟨Sum.map f id,f.hom.continuous.sumMap continuous_id⟩
  point := rfl

/-- Restriction to the original summand of a map from the disjoint-point
space is an exact equivalence with arbitrary continuous maps. -/
def adjoinPointEquiv (A : TopCat.{u}) (X : BasedSpace.{u}) :
    (adjoinPoint A ⟶ X) ≃ C(A,X) where
  toFun f := f.map.comp ⟨Sum.inl,continuous_inl⟩
  invFun f :=
    ⟨⟨Sum.elim f (fun _ => X.point),f.continuous.sumElim continuous_const⟩,rfl⟩
  left_inv f := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    cases z with
    | inl a => rfl
    | inr p => exact f.point.symm
  right_inv f := rfl

end KIP126.AdamsSynthetic.Source.BasedSpace
