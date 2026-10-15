module

public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

def tail (X : Prespectrum.{0}) : Prespectrum.{0} where
  level n := X.level (n+1)
  bond n := X.bond (n+1)
  bond_point n := X.bond_point (n+1)
  bond_zero n := X.bond_zero (n+1)
  bond_one n := X.bond_one (n+1)

def tailMap {X Y : Prespectrum.{0}} (f : X ⟶ Y) : X.tail ⟶ Y.tail where
  level n := f.level (n+1)
  point n := f.point (n+1)
  bond n := f.bond (n+1)

end Prespectrum
end KIP126.StableHomotopy.Spectra
