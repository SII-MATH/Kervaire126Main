module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open Topology
open scoped Topology.Homotopy unitInterval

universe u

/-- The actual bond map on the level homotopy quotients. -/
def stabilizeHomotopy (X : Prespectrum.{u}) (n r : ℕ) :
    _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point →
      _root_.HomotopyGroup (Fin (r + 1)) (X.level (n + 1)) (X.level (n + 1)).point :=
  Quotient.map (stabilizeLoop X n r) (fun _ _ h => stabilizeLoop_homotopic X n r _ _ h)

end KIP126.StableHomotopy.Spectra.Prespectrum
