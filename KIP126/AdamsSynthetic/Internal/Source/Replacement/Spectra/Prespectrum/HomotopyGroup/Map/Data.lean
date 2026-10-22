module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyGroup/Map/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Abelian.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped Topology.Homotopy

universe u

/-- Postcomposition of actual cubical loops with a prespectrum map. -/
def Hom.levelLoop {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop (Fin r) (Y.level n) (Y.level n).point :=
  ⟨(f.level n).comp p.val, fun t ht => by
    change f.level n (p t) = _
    exact (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩

/-- The induced map on the actual level homotopy quotients. -/
def Hom.levelHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ) :
    _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point →
      _root_.HomotopyGroup (Fin r) (Y.level n) (Y.level n).point :=
  Quotient.map (f.levelLoop n r) (fun _ _ h => h.comp_continuousMap (f.level n))

end KIP126.AdamsSynthetic.Source.Prespectrum
