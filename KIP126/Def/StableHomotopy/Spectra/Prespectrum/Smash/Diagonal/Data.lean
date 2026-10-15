module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Bond

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

noncomputable def diagonalSmash (X Y : Prespectrum.{0}) : Prespectrum.{0} where
  level := diagonalLevel X Y
  bond := diagonalBond X Y
  bond_point n := (diagonalBond_laws X Y n).1
  bond_zero n := (diagonalBond_laws X Y n).2.1
  bond_one n := (diagonalBond_laws X Y n).2.2

noncomputable def diagonalMapLevel {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n, diagonalLevel X Y n ⟶ diagonalLevel X' Y' n
  | 0 => BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩
  | 1 => BasedSpace.suspendMap
      (BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩)
  | n+2 => diagonalMapLevel (tailMap f) (tailMap g) n

end Prespectrum
end KIP126.StableHomotopy.Spectra
