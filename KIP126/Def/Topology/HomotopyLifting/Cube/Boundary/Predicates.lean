module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval

universe u v

/-- The actual right lifting property against all finite cube boundary
inclusions, with the full boundary and comparison retained pointwise. -/
def HasCubeBoundaryLifting {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (f : C(E,B)) : Prop :=
  ∀ (n : ℕ) (g : C(↥(_root_.Cube.boundary (Fin n)),E)) (H : C(Fin n → I,B)),
    (∀ z, f (g z) = H z.val) →
    ∃ L : C(Fin n → I,E), (∀ z, f (L z) = H z) ∧ (∀ z, L z.val = g z)

end KIP126.Topology.HomotopyLifting
