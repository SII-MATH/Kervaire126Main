module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum
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

end KIP126.StableHomotopy.Spectra.Prespectrum
