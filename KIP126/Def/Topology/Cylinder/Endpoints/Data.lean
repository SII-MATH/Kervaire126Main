module

public import KIP126.Def.Topology.HomotopyExtension.Retraction.Proofs

@[expose] public section

namespace KIP126.Topology
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal inclusion of both ends of an arbitrary space cylinder. -/
def cylinderEndpointInclusion (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ TopCat.of (A × I) :=
  TopCat.ofHom ⟨Sum.elim (fun a => (a,0)) (fun a => (a,1)),
    (continuous_id.prodMk continuous_const).sumElim (continuous_id.prodMk continuous_const)⟩

end KIP126.Topology
