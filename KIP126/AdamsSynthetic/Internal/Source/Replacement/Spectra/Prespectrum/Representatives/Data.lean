module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Representatives/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Sphere.Representatives.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

/-- The sphere cube mapped into the generating stage of the actual free prespectrum. -/
noncomputable def freeSphereLoop (n r : ℕ) :
    GenLoop (Fin r) ((free n (sphereLevel r)).level n)
      ((free n (sphereLevel r)).level n).point := by
  let e := freeEvaluation n (sphereLevel r) (free n (sphereLevel r)) (𝟙 _)
  exact ⟨e.map.comp (sphereCube r).val, fun t ht => by
    change e.map (sphereCube r t) = _
    exact (congrArg e.map ((sphereCube r).property t ht)).trans e.point⟩

/-- The stable class of the canonical generator in a shifted free sphere. -/
noncomputable def freeSphereGenerator (d : ℤ) (n r : ℕ) (h : (r : ℤ) = d + n) :
    StableHomotopy (free n (sphereLevel r)) d :=
  loopClass _ d n r h (freeSphereLoop n r)

end KIP126.AdamsSynthetic.Source.Prespectrum
