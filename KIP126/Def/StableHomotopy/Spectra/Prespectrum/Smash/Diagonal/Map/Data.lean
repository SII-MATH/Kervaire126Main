module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

noncomputable def diagonalSmashMap {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') : diagonalSmash X Y ⟶ diagonalSmash X' Y' where
  level n := (diagonalMapLevel f g n).map
  point n := (diagonalMapLevel f g n).point
  bond n := diagonalMapLevel_bond f g n

end Prespectrum
end KIP126.StableHomotopy.Spectra
