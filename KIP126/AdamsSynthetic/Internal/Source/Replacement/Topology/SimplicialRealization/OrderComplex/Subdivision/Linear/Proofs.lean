module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Vector.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The geometric barycenter of an actual chain evaluates to its
uniform vector average. -/
theorem sum_smul_orderChainBarycenter (P : Type u) [PartialOrder P] [Fintype P]
    (v : P → E) (c : PartialOrder.NonemptyFiniteChains P) :
    (∑ p, orderChainBarycenter P c p • v p) = orderSubdivisionVertices v c := by
  classical
  simp only [orderChainBarycenter_apply, ite_smul, zero_smul,
    orderSubdivisionVertices, Simplex.BarycentricSubdivisionMesh.avg, Finset.smul_sum]
  rw [← Finset.sum_filter]
  simp

/-- The actual subdivision coordinates evaluate linearly to the
ordinary coordinates on the subdivided order with its averaged vertices. -/
theorem sum_smul_orderSubdivisionCoordinates (P : Type u) [PartialOrder P] [Fintype P]
    [Fintype (PartialOrder.NonemptyFiniteChains P)] (v : P → E)
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    (∑ p, orderSubdivisionCoordinates P x p • v p) =
      ∑ c, orderComplexCoordinates (PartialOrder.NonemptyFiniteChains P) x c •
        orderSubdivisionVertices v c := by
  obtain ⟨d,s,w,_,_,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  rw [← hs, orderSubdivisionCoordinates_simplex, orderComplexCoordinates_simplex,
    Simplex.sum_smul_map]
  change (∑ p, Simplex.combinationCoordinates
    (fun k => orderChainBarycenter P (s.obj k)) w p • v p) = _
  rw [Simplex.sum_smul_combinationCoordinates]
  simp only [sum_smul_orderChainBarycenter]

end KIP126.Topology.SimplicialRealization
