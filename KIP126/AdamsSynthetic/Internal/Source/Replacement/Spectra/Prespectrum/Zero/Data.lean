module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Zero/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
universe u

/-- The actual prespectrum with one point at every level. -/
def zeroPrespectrum : Prespectrum.{u} where
  level _ := { space := TopCat.of PUnit, point := PUnit.unit }
  bond _ := ContinuousMap.const _ PUnit.unit
  bond_point _ _ := rfl
  bond_zero _ _ := rfl
  bond_one _ _ := rfl

/-- The actual constant based map, level by level. -/
def zeroMap (X Y : Prespectrum.{u}) : X ⟶ Y where
  level n := ContinuousMap.const _ (Y.level n).point
  point _ := rfl
  bond n _ t := (Y.bond_point n t).symm

end KIP126.AdamsSynthetic.Source.Prespectrum
