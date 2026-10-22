module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyGroup/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open Topology
open scoped Topology.Homotopy unitInterval

universe u

/-- The actual bond map on the level homotopy quotients. -/
def stabilizeHomotopy (X : Prespectrum.{u}) (n r : ℕ) :
    _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point →
      _root_.HomotopyGroup (Fin (r + 1)) (X.level (n + 1)) (X.level (n + 1)).point :=
  Quotient.map (stabilizeLoop X n r) (fun _ _ h => stabilizeLoop_homotopic X n r _ _ h)

end KIP126.AdamsSynthetic.Source.Prespectrum
