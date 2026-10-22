module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricSubdivisionMesh.Proofs
import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open Simplex.BarycentricSubdivisionMesh

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Increasing the numerical bound preserves an actual order mesh bound. -/
theorem OrderMeshBound.mono {P : Type u} [PartialOrder P] {v : P → E} {D D' : ℝ}
    (h : OrderMeshBound P v D) (hDD' : D ≤ D') : OrderMeshBound P v D' :=
  fun c p hp q hq => (h c p hp q hq).trans hDD'

/-- Barycentric subdivision contracts the actual vertex mesh, with a
factor depending only on the chain-size bound of the original order. -/
theorem OrderMeshBound.subdivision {P : Type u} [PartialOrder P] {v : P → E}
    {N : ℕ} {D : ℝ} (h : OrderMeshBound P v D) (hP : OrderChainSizeLE P N)
    (hN : 0 < N) (hD : 0 ≤ D) :
    OrderMeshBound (PartialOrder.NonemptyFiniteChains P) (orderSubdivisionVertices v)
      ((1 - 1 / (N : ℝ)) * D) := by
  intro c a ha b hb
  obtain hab | hba := c.comparable ⟨a, ha⟩ ⟨b, hb⟩
  · exact dist_avg_subset_le_card_bound v hab a.nonempty N hN (hP b) D hD (h b)
  · rw [dist_comm]
    exact dist_avg_subset_le_card_bound v hba b.nonempty N hN (hP a) D hD (h a)

/-- The same original chain-size bound holds at every actual subdivision depth. -/
theorem orderChainSizeLE_iterated (P : Type u) [PartialOrder P] {N : ℕ}
    (hP : OrderChainSizeLE P N) (n : ℕ) : OrderChainSizeLE (iteratedOrderSubdivision P n) N := by
  induction n with
  | zero => exact hP
  | succ n ih => exact orderChainSizeLE_subdivision (iteratedOrderSubdivision P n) ih

/-- Repeated actual averaging over nonempty chains has the geometric
mesh estimate with the fixed original contraction factor. -/
theorem OrderMeshBound.iterated {P : Type u} [PartialOrder P] {v : P → E}
    {N : ℕ} {D : ℝ} (h : OrderMeshBound P v D) (hP : OrderChainSizeLE P N)
    (hN : 0 < N) (hD : 0 ≤ D) (n : ℕ) :
    OrderMeshBound (iteratedOrderSubdivision P n) (iteratedOrderSubdivisionVertices v n)
      ((1 - 1 / (N : ℝ)) ^ n * D) := by
  induction n with
  | zero =>
    change OrderMeshBound P v ((1 - 1 / (N : ℝ)) ^ 0 * D)
    simpa only [pow_zero, one_mul] using h
  | succ n ih =>
    change OrderMeshBound (PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n))
      (orderSubdivisionVertices (iteratedOrderSubdivisionVertices v n))
      ((1 - 1 / (N : ℝ)) ^ (n + 1) * D)
    have hs := ih.subdivision (orderChainSizeLE_iterated P hP n) hN
      (mul_nonneg (pow_nonneg (contraction_nonneg N hN) n) hD)
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hs

/-- Every convex pair in one actual order simplex inherits its vertex mesh bound. -/
theorem OrderMeshBound.combinations {P : Type u} [PartialOrder P] {v : P → E}
    {D : ℝ} (h : OrderMeshBound P v D) (c : PartialOrder.NonemptyFiniteChains P)
    (t s : stdSimplex ℝ c.finset) :
    dist (∑ p : c.finset, t p • v p.val) (∑ p : c.finset, s p • v p.val) ≤ D :=
  dist_combination_combination_le _ _ t s D (fun p q => h c p p.property q q.property)

/-- The fixed original contraction factor eventually reduces any nonnegative
mesh bound below any positive tolerance. -/
theorem exists_orderMesh_power_lt {N : ℕ} {D : ℝ} (hN : 0 < N) (hD : 0 ≤ D)
    (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, (1 - 1 / (N : ℝ)) ^ n * D < ε := by
    by_cases hzero : D = 0
    · exact ⟨0, by simp [hzero, hε]⟩
    · have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) (contraction_lt_one N hN)
      exact ⟨n, (lt_div_iff₀ hpos).mp hn⟩

/-- Every positive tolerance is reached by a finite number of actual
subdivisions, uniformly for all vertices in each resulting order simplex. -/
theorem OrderMeshBound.exists_iterated_small {P : Type u} [PartialOrder P] {v : P → E}
    {N : ℕ} {D : ℝ} (h : OrderMeshBound P v D) (hP : OrderChainSizeLE P N)
    (hN : 0 < N) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ c : PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n),
      ∀ p ∈ c.finset, ∀ q ∈ c.finset,
        dist (iteratedOrderSubdivisionVertices v n p)
          (iteratedOrderSubdivisionVertices v n q) < ε := by
  obtain ⟨n, hn⟩ := exists_orderMesh_power_lt hN hD ε hε
  exact ⟨n, fun c p hp q hq => (h.iterated hP hN hD n c p hp q hq).trans_lt hn⟩

/-- The same subdivision depth bounds the distance of all points of each
simplex, including its boundary, through their actual vertex combinations. -/
theorem OrderMeshBound.exists_iterated_combinations_small
    {P : Type u} [PartialOrder P] {v : P → E}
    {N : ℕ} {D : ℝ} (h : OrderMeshBound P v D) (hP : OrderChainSizeLE P N)
    (hN : 0 < N) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ c : PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n),
      ∀ t s : stdSimplex ℝ c.finset,
        dist (∑ p : c.finset, t p • iteratedOrderSubdivisionVertices v n p.val)
          (∑ p : c.finset, s p • iteratedOrderSubdivisionVertices v n p.val) < ε := by
  obtain ⟨n, hn⟩ := exists_orderMesh_power_lt hN hD ε hε
  exact ⟨n, fun c t s => ((h.iterated hP hN hD n).combinations c t s).trans_lt hn⟩

end KIP126.Topology.SimplicialRealization
