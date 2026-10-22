module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- Uniform barycentric coordinates on a nonempty finite chain. -/
noncomputable def orderChainBarycenter (P : Type u) [PartialOrder P] [Fintype P]
    (c : PartialOrder.NonemptyFiniteChains P) : stdSimplex ℝ P := by
  letI : Nonempty c.finset := c.nonempty.to_subtype
  exact stdSimplex.map (fun a : c.finset => a.val) stdSimplex.barycenter

/-- Every flag of chains is sent to the affine simplex on the uniform
barycenters of its chains, inside the actual singular set. -/
noncomputable def orderSubdivisionCoordinatesAdjoint (P : Type u)
    [PartialOrder P] [Fintype P] :
    nerve (PartialOrder.NonemptyFiniteChains P) ⟶
      TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ P)) where
  app d := TypeCat.ofHom fun s =>
    (TopCat.toSSetObjEquiv _ _).symm
      (simplexCombination (fun k => orderChainBarycenter P (s.obj k)))
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro t
    apply stdSimplex.ext
    exact (Simplex.combinationCoordinates_map
      (A := Fin (e.unop.len+1)) (B := Fin (d.unop.len+1)) (C := P)
      f.unop (fun k => orderChainBarycenter P (s.obj k)) t).symm

/-- Actual geometric subdivision coordinates for any finite partial
order; unlike a construction on arbitrary simplicial sets, its faces
remain honest chains. -/
noncomputable def orderSubdivisionCoordinates (P : Type u)
    [PartialOrder P] [Fintype P] :
    C(|nerve (PartialOrder.NonemptyFiniteChains P)|,stdSimplex ℝ P) :=
  ((sSetTopAdj.homEquiv _ _).symm (orderSubdivisionCoordinatesAdjoint P)).hom

end KIP126.Topology.SimplicialRealization
