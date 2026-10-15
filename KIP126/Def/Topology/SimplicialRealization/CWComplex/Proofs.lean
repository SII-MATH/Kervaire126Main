module

public import KIP126.Def.Topology.SimplicialRealization.CWComplex.Data
public import KIP126.Def.Topology.CWComplex.ClosedEmbedding.Proofs
public import KIP126.Def.Topology.CWComplex.Hausdorff.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual geometric realization of every simplicial set is Hausdorff. -/
theorem realization_t2Space (X : SSet.{u}) : T2Space |X| :=
  KIP126.Topology.cwComplex_t2Space (cwComplex X)

end KIP126.Topology.SimplicialRealization
