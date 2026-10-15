module

public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual geometric realization identifies a simplicial equality locus
with the literal topological equality locus, with its subspace topology. -/
noncomputable def equalityHomeomorph {X Y : SSet.{u}} (f g : X ⟶ Y) :
    |(equalitySubcomplex f g).toSSet| ≃ₜ
      {x : |X| // SSet.toTop.map f x = SSet.toTop.map g x} :=
  (equalityComparison_isClosedEmbedding f g).isEmbedding.toHomeomorphOfSurjective
    (equalityComparison_surjective f g)


end KIP126.Topology.SimplicialRealization
