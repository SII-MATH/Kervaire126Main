module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- The actual finite-order subdivision homeomorphism with barycentric
coordinates, chosen from its proved existence theorem. -/
noncomputable def orderSubdivisionHomeomorph (P : Type u) [PartialOrder P] [Fintype P] :
    |nerve (PartialOrder.NonemptyFiniteChains P)| ≃ₜ |nerve P| :=
  Classical.choose (exists_orderSubdivision_homeomorph P)

/-- A finite vertex enumeration at every actual subdivision depth. -/
@[implicit_reducible]
noncomputable def iteratedOrderSubdivisionFintype (P : Type u) [PartialOrder P] [Fintype P] :
    (n : ℕ) → Fintype (iteratedOrderSubdivision P n) := fun n => match n with
  | 0 => inferInstanceAs (Fintype P)
  | n + 1 => by
    change Fintype (PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n))
    letI := iteratedOrderSubdivisionFintype P n
    letI := finite_nonemptyFiniteChains (iteratedOrderSubdivision P n)
    exact Fintype.ofFinite _

/-- Repeated subdivision gives actual homeomorphisms of realizations,
formed by composing the proved one-step barycentric homeomorphisms. -/
noncomputable def iteratedOrderSubdivisionHomeomorph (P : Type u)
    [PartialOrder P] [Fintype P] :
    (n : ℕ) → |nerve (iteratedOrderSubdivision P n)| ≃ₜ |nerve P| := fun n => match n with
  | 0 => Homeomorph.refl _
  | n + 1 => by
    letI := iteratedOrderSubdivisionFintype P n
    change |nerve (PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n))| ≃ₜ |nerve P|
    exact (orderSubdivisionHomeomorph (iteratedOrderSubdivision P n)).trans
      (iteratedOrderSubdivisionHomeomorph P n)

end KIP126.Topology.SimplicialRealization
