module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Realization/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Opposite Simplicial

universe u

/-- The actual realization with the specified simplicial vertex as basepoint. -/
noncomputable def basedRealization (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    BasedSpace.{u} where
  space := SSet.toTop.obj K
  point := TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app K).app (op ⦋0⦌) v)

end KIP126.AdamsSynthetic.Source
