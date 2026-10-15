module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cells.Data
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Free.Geometry.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Free.Lifting.Proofs
public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.AdjoinPoint.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory _root_.Topology
open KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

instance cubicalCellTarget_level_compactSpace (i : ℕ × ℕ) (n : ℕ) :
    CompactSpace ((cubicalCellTarget.{u} i).level n) := by
  letI : CompactSpace (cubeObject.{u} i.2) :=
    inferInstanceAs (CompactSpace (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (Fin i.2 → I)))
  exact (free_level_compact_t2 i.1 (BasedSpace.adjoinPoint (cubeObject.{u} i.2)) n).1

instance cubicalCellTarget_level_t2Space (i : ℕ × ℕ) (n : ℕ) :
    T2Space ((cubicalCellTarget.{u} i).level n) := by
  letI : CompactSpace (cubeObject.{u} i.2) :=
    inferInstanceAs (CompactSpace (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (Fin i.2 → I)))
  exact (free_level_compact_t2 i.1 (BasedSpace.adjoinPoint (cubeObject.{u} i.2)) n).2

/-- Every actual free cubical cell inclusion is a genuine closed
embedding at every level. -/
theorem cubicalCellBoundary_level_isClosedEmbedding (i : ℕ × ℕ) (n : ℕ) :
    IsClosedEmbedding ((cubicalCellBoundary.{u} i).level n) := by
  letI : CompactSpace (cubeObject.{u} i.2) :=
    inferInstanceAs (CompactSpace (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeBoundaryObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (↥(_root_.Cube.boundary (Fin i.2)))))
  exact freeMap_level_isClosedEmbedding i.1 _
    (BasedSpace.adjoinPointMap_injective _ (cubeBoundaryInclusion_isClosedEmbedding i.2).injective) n

end KIP126.StableHomotopy.Spectra.Prespectrum
