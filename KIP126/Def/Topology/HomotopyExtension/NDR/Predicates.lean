module

public import KIP126.Def.Topology.HomotopyExtension.Data

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open scoped unitInterval

/-- Actual neighborhood deformation data for a specified subset of a space.
The displayed zero set, homotopy and endpoint condition are all literal. -/
def IsNDRData {X : Type*} [TopologicalSpace X] (S : Set X)
    (u : C(X,I)) (h : C(X × I,X)) : Prop :=
  (∀ x, u x = 0 ↔ x ∈ S) ∧
  (∀ x, h (x,0) = x) ∧
  (∀ x ∈ S, ∀ t, h (x,t) = x) ∧
  (∀ x, u x < 1 → h (x,1) ∈ S)

end KIP126.Topology.HomotopyExtension
