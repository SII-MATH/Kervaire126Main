module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Abelian.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

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

end KIP126.StableHomotopy.Spectra.Prespectrum
