module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Linear.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- The chosen actual subdivision homeomorphism has the proved
barycentric coordinates at every point. -/
theorem orderSubdivisionHomeomorph_coordinates (P : Type u)
    [PartialOrder P] [Fintype P]
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    orderComplexCoordinates P (orderSubdivisionHomeomorph P x) =
      orderSubdivisionCoordinates P x :=
  Classical.choose_spec (exists_orderSubdivision_homeomorph P) x

/-- The zero-fold actual subdivision homeomorphism is the identity. -/
theorem iteratedOrderSubdivisionHomeomorph_zero (P : Type u)
    [PartialOrder P] [Fintype P] (x : |nerve P|) :
    iteratedOrderSubdivisionHomeomorph P 0 x = x := rfl

/-- The actual iterated homeomorphism composes the newest barycentric
homeomorphism with all the preceding ones. -/
theorem iteratedOrderSubdivisionHomeomorph_succ (P : Type u)
    [PartialOrder P] [Fintype P] (n : ℕ)
    (x : |nerve (iteratedOrderSubdivision P (n+1))|) :
    iteratedOrderSubdivisionHomeomorph P (n+1) x =
      iteratedOrderSubdivisionHomeomorph P n
        (@orderSubdivisionHomeomorph (iteratedOrderSubdivision P n) _
          (iteratedOrderSubdivisionFintype P n) x) := rfl

/-- The actual iterated homeomorphism evaluates in the original vertex
vectors exactly as the recursively averaged subdivision vertices.
Thus the geometric mesh estimates apply to these actual maps. -/
theorem iteratedOrderSubdivisionHomeomorph_sum_smul (P : Type u)
    [PartialOrder P] [Fintype P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : P → E) (n : ℕ) (x : |nerve (iteratedOrderSubdivision P n)|) :
    letI := iteratedOrderSubdivisionFintype P n
    (∑ p, orderComplexCoordinates P (iteratedOrderSubdivisionHomeomorph P n x) p • v p) =
      ∑ q, orderComplexCoordinates (iteratedOrderSubdivision P n) x q •
        iteratedOrderSubdivisionVertices v n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    letI := iteratedOrderSubdivisionFintype P n
    letI := iteratedOrderSubdivisionFintype P (n+1)
    letI : Fintype (PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n)) :=
      iteratedOrderSubdivisionFintype P (n+1)
    change (∑ p, orderComplexCoordinates P
        (iteratedOrderSubdivisionHomeomorph P (n+1) x) p • v p) =
      ∑ q : PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n),
        orderComplexCoordinates _ x q • orderSubdivisionVertices (iteratedOrderSubdivisionVertices v n) q
    rw [iteratedOrderSubdivisionHomeomorph_succ,ih,orderSubdivisionHomeomorph_coordinates]
    exact sum_smul_orderSubdivisionCoordinates _ (iteratedOrderSubdivisionVertices v n) x

/-- On every actual simplex of every subdivision, the composed geometric
homeomorphism is the affine simplex on the recursively averaged vertices. -/
theorem iteratedOrderSubdivisionHomeomorph_simplex_sum_smul (P : Type u)
    [PartialOrder P] [Fintype P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : P → E) (n d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (Opposite.op ⦋d⦌))
    (w : stdSimplex ℝ (Fin (d+1))) :
    (∑ p, orderComplexCoordinates P
      (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s w)) p • v p) =
      ∑ k, w k • iteratedOrderSubdivisionVertices v n (s.obj k) := by
  letI := iteratedOrderSubdivisionFintype P n
  rw [iteratedOrderSubdivisionHomeomorph_sum_smul,orderComplexCoordinates_simplex,
    Simplex.sum_smul_map]

end KIP126.Topology.SimplicialRealization
