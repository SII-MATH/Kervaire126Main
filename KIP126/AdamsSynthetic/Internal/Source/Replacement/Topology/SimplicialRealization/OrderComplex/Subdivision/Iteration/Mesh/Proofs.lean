module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual realized simplex shrinks by the iterated mesh factor
under the actual composed subdivision homeomorphism. -/
theorem iteratedOrderSubdivisionHomeomorph_simplex_mesh (P : Type u)
    [PartialOrder P] [Fintype P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : P → E) {N : ℕ} {D : ℝ} (hv : OrderMeshBound P v D)
    (hP : OrderChainSizeLE P N) (hN : 0 < N) (hD : 0 ≤ D)
    (n d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (op ⦋d⦌))
    (w z : stdSimplex ℝ (Fin (d+1))) :
    dist
      (∑ p, orderComplexCoordinates P
        (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s w)) p • v p)
      (∑ p, orderComplexCoordinates P
        (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s z)) p • v p) ≤
      (1 - 1 / (N : ℝ)) ^ n * D := by
  classical
  rw [iteratedOrderSubdivisionHomeomorph_simplex_sum_smul,
    iteratedOrderSubdivisionHomeomorph_simplex_sum_smul]
  let c : PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n) := {
    finset := Finset.univ.image s.obj
    nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    comparable := by
      rintro ⟨a,ha⟩ ⟨b,hb⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      exact (le_total i j).imp (fun h => s.monotone h) (fun h => s.monotone h) }
  apply Simplex.BarycentricSubdivisionMesh.dist_combination_combination_le
  intro i j
  exact hv.iterated hP hN hD n c (s.obj i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    (s.obj j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)

/-- A positive tolerance bounds every point pair of every actual
simplex after a single sufficiently large subdivision depth. -/
theorem exists_iteratedOrderSubdivisionHomeomorph_simplex_small (P : Type u)
    [PartialOrder P] [Fintype P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : P → E) {N : ℕ} {D : ℝ} (hv : OrderMeshBound P v D)
    (hP : OrderChainSizeLE P N) (hN : 0 < N) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (op ⦋d⦌))
      (w z : stdSimplex ℝ (Fin (d+1))),
      dist
        (∑ p, orderComplexCoordinates P
          (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s w)) p • v p)
        (∑ p, orderComplexCoordinates P
          (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s z)) p • v p) < ε := by
  obtain ⟨n,hn⟩ := exists_orderMesh_power_lt hN hD ε hε
  exact ⟨n,fun d s w z =>
    (iteratedOrderSubdivisionHomeomorph_simplex_mesh P v hv hP hN hD n d s w z).trans_lt hn⟩

/-- Standard coordinate vertices recover the original simplex vector exactly. -/
theorem sum_smul_coordinate_vertices {P : Type u} [Fintype P]
    (y : stdSimplex ℝ P) :
    (∑ p, y p • Pi.single p (1 : ℝ)) = y.val := by
  classical
  funext q
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  rfl

/-- The actual coordinate realizations of all simplices become uniformly
small after finitely many genuine subdivision homeomorphisms. -/
theorem exists_iteratedOrderSubdivision_coordinates_small (P : Type u)
    [PartialOrder P] [Fintype P] (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (op ⦋d⦌))
      (w z : stdSimplex ℝ (Fin (d+1))),
      dist
        (orderComplexCoordinates P
          (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s w)))
        (orderComplexCoordinates P
          (iteratedOrderSubdivisionHomeomorph P n (simplexPoint _ s z))) < ε := by
  classical
  let v (p : P) : P → ℝ := Pi.single p 1
  have hv : OrderMeshBound P v 1 := by
    intro c p _ q _
    apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro r
    by_cases hp : p = r <;> by_cases hq : q = r <;>
      simp [v,hp,hq,Real.dist_eq]
  have hP : OrderChainSizeLE P (Fintype.card P+1) :=
    fun c => (Finset.card_le_univ c.finset).trans (Nat.le_succ _)
  obtain ⟨n,hn⟩ := exists_iteratedOrderSubdivisionHomeomorph_simplex_small P v hv hP
    (Nat.succ_pos _) (by norm_num) ε hε
  refine ⟨n,?_⟩
  intro d s w z
  simpa only [v,sum_smul_coordinate_vertices,Subtype.dist_eq] using hn d s w z

end KIP126.Topology.SimplicialRealization
