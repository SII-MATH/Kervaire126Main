module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/FiniteSupport/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory

universe u

namespace BasedSpace

/-- A subspace containing the specified basepoint, with its actual subspace topology. -/
def subspace (X : BasedSpace.{u}) (S : Set X) (hp : X.point ∈ S) : BasedSpace.{u} where
  space := TopCat.of S
  point := ⟨X.point,hp⟩

/-- The actual based inclusion of a subspace. -/
def subspaceInclusion (X : BasedSpace.{u}) (S : Set X) (hp : X.point ∈ S) :
    X.subspace S hp ⟶ X :=
  ⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩

end BasedSpace

namespace Prespectrum

/-- The free map induced by a based map, using the actual free/evaluation adjunction. -/
noncomputable def freeMap (n : ℕ) {A B : BasedSpace.{u}} (f : A ⟶ B) :
    free n A ⟶ free n B :=
  (freeEvaluation n A (free n B)).symm
    (f ≫ freeEvaluation n B (free n B) (𝟙 _))

end Prespectrum

end KIP126.AdamsSynthetic.Source
