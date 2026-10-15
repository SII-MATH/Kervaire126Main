module

public import KIP126.Def.Topology.HomotopyLifting.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval
universe u v w

/-- Relative homotopy lifting for the pair `(Z,S)`, stated on the actual
bottom-and-side subspace, with no chosen lifting function. -/
def HasRelativeLifting {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (f : C(E,B))
    (Z : Type w) [TopologicalSpace Z] (S : Set Z) : Prop :=
  ∀ (g : C(CylinderHorn Z S,E)) (H : C(I × Z,B)),
    (∀ z, f (g z) = H z.val) →
    ∃ L : C(I × Z,E), (∀ z, f (L z) = H z) ∧ (∀ z, L z.val = g z)

/-- Relative lifting for all finite cube boundary pairs. -/
def HasCubicalLifting {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (f : C(E,B)) : Prop :=
  ∀ n : ℕ, HasRelativeLifting f (Fin n → I) (_root_.Cube.boundary (Fin n))

end KIP126.Topology.HomotopyLifting
