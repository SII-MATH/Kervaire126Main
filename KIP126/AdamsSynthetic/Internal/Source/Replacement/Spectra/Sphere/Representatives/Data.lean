module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Sphere/Representatives/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

/-- The actual cubical generator of the iterated reduced suspension sphere. -/
def sphereCube : ∀ n, GenLoop (Fin n) (sphereLevel n) (sphereLevel n).point
  | 0 => ⟨ContinuousMap.const _ (show sphereLevel 0 from (1 : Fin 2)), by
      intro t ht
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i⟩
  | n + 1 => stabilizeLoop sphere n n (sphereCube n)

end KIP126.AdamsSynthetic.Source.Prespectrum
