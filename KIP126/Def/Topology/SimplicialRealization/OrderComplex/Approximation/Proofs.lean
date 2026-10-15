module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Stars.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Carrier.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual continuous map between finite order complexes admits
a vertex star assignment after finitely many actual subdivisions. -/
theorem exists_iteratedOrderSubdivision_star_assignment (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : C(|nerve P|,|nerve Q|)) :
    ∃ n : ℕ, letI := iteratedOrderSubdivisionFintype P n
      ∃ v : iteratedOrderSubdivision P n → Q,
        IsOrderStarAssignment
          (f.comp ⟨iteratedOrderSubdivisionHomeomorph P n,
            (iteratedOrderSubdivisionHomeomorph P n).continuous⟩) v := by
  let U (q : Q) := f ⁻¹' orderOpenStar Q q
  have hU (q : Q) : IsOpen (U q) := (isOpen_orderOpenStar Q q).preimage f.continuous
  have hcover : (⋃ q, U q) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion,U,Set.mem_preimage,Set.mem_univ,iff_true]
    exact exists_mem_orderOpenStar Q (f x)
  obtain ⟨n,hn⟩ := exists_iteratedOrderSubdivision_star_refinement P U hU hcover
  refine ⟨n,?_⟩
  letI := iteratedOrderSubdivisionFintype P n
  choose v hv using hn
  exact ⟨v,fun p x hx => hv p x hx⟩

/-- A star assignment necessarily chooses the prescribed vertex on
any source star meeting a point sent to that vertex. -/
theorem IsOrderStarAssignment.eq_of_vertex {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v)
    {p : P} {x : |nerve P|} (hx : x ∈ orderOpenStar P p)
    {q : Q} (hf : f x = orderVertex Q q) : v p = q := by
  have hp := h p hx
  change 0 < orderComplexCoordinates Q (f x) (v p) at hp
  rw [hf,orderComplexCoordinates_vertex] at hp
  by_contra hn
  simp [stdSimplex.vertex,Ne.symm hn] at hp

end KIP126.Topology.SimplicialRealization
