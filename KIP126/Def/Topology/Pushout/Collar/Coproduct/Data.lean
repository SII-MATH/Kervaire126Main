module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocalAtTarget

@[expose] public section

namespace KIP126.Topology

/-- A subspace of a topological disjoint union is the disjoint union of
the corresponding subspaces, with their actual subspace topologies. -/
def sigmaSubtypeHomeomorph {ι : Type*} (A : ι → Type*)
    [∀ i, TopologicalSpace (A i)] (W : ∀ i, Set (A i)) :
    (Σ i, W i) ≃ₜ {x : Σ i, A i // x.2 ∈ W x.1} := by
  let e : (Σ i, W i) ≃ {x : Σ i, A i // x.2 ∈ W x.1} := {
    toFun := fun x => ⟨⟨x.1, x.2.val⟩, x.2.property⟩
    invFun := fun x => ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine e.toHomeomorphOfContinuousOpen ?_ ?_
  · exact continuous_sigma (fun _ =>
      (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _)
  · exact isOpenMap_sigma.mpr (fun i =>
      (isOpenMap_sigmaMk (i := i)).restrictPreimage {x : Σ i, A i | x.2 ∈ W x.1})

end KIP126.Topology
