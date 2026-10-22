module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/Order/Initial.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Zero.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Data

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization
open KIP126.Topology.HomotopyLifting

universe u

/-- The actual initial one-point level is homeomorphic to an actual finite
order realization, using the zero-dimensional cube-cone comparison. -/
noncomputable def zeroPrespectrumLevelOrderHomeomorph (n : ℕ) :
    |nerve (WithTop (orderProperChains (ULift.{u} (Fin 1))))| ≃ₜ
      (zeroPrespectrum.{u}.level n) := by
  letI : Unique (cubeObject.{u} 0) :=
    inferInstanceAs (Unique (ULift.{u} (Fin 0 → unitInterval)))
  letI : Unique (zeroPrespectrum.{u}.level n) := inferInstanceAs (Unique PUnit)
  exact (orderBoundaryConeCubeHomeomorph.{u} 0).trans (Homeomorph.homeomorphOfUnique _ _)

end KIP126.AdamsSynthetic.Source.Prespectrum

end

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization

universe u

/-- The actual cone vertex represents the specified initial basepoint. -/
theorem zeroPrespectrumLevelOrderHomeomorph_vertex (n : ℕ) :
    zeroPrespectrumLevelOrderHomeomorph.{u} n
      (orderVertex _ (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1))))) =
        (zeroPrespectrum.{u}.level n).point := by
  letI : Subsingleton (zeroPrespectrum.{u}.level n) := inferInstanceAs (Subsingleton PUnit)
  exact Subsingleton.elim _ _

/-- The inverse initial model sends the original basepoint to that same
actual cone vertex, retaining the point needed for later based comparisons. -/
theorem zeroPrespectrumLevelOrderHomeomorph_symm_point (n : ℕ) :
    (zeroPrespectrumLevelOrderHomeomorph.{u} n).symm
      (zeroPrespectrum.{u}.level n).point =
        orderVertex _ (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1)))) := by
  apply (zeroPrespectrumLevelOrderHomeomorph n).injective
  rw [(zeroPrespectrumLevelOrderHomeomorph n).apply_symm_apply,
    zeroPrespectrumLevelOrderHomeomorph_vertex]

end KIP126.AdamsSynthetic.Source.Prespectrum

end
