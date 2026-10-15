module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Charts.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open Simplicial

universe u

/-- The actual classical CW structure, retaining its explicit nondegenerate
simplex indexing for finite-support and cellular constructions. -/
@[reducible] noncomputable def realizationClassicalCWComplex (X : SSet.{u}) :
    _root_.Topology.CWComplex (Set.univ : Set |X|) where
  cell := fun n => X.nonDegenerate n
  map := simplexCellChart X
  source_eq := fun _ _ => rfl
  continuousOn := simplexCharacteristicExtension_continuousOn X
  continuousOn_symm := simplexCellChart_continuousOn_symm X
  pairwiseDisjoint' := simplexCellChart_pairwiseDisjoint X
  mapsTo' := simplexCellChart_boundary X
  closed' := fun A _ => simplexCellChart_closed X A
  union' := simplexCellChart_union X

end KIP126.Topology.SimplicialRealization
