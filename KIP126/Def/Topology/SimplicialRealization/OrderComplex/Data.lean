module

public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Barycentric.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The canonical singular simplex of a finite order simplex sends its
weights to the corresponding vertices of the order. -/
noncomputable def orderComplexCoordinatesAdjoint (P : Type u)
    [PartialOrder P] [Fintype P] :
    nerve P ⟶ TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ P)) where
  app d := TypeCat.ofHom fun s =>
    (TopCat.toSSetObjEquiv _ _).symm
      ⟨stdSimplex.map s.obj,stdSimplex.continuous_map s.obj⟩
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro t
    change stdSimplex.map (s.obj ∘ f.unop) t =
      stdSimplex.map s.obj (stdSimplex.map f.unop t)
    exact (stdSimplex.map_comp_apply f.unop s.obj t).symm

/-- The actual realization's continuous coordinate map into the
standard simplex on the finite vertex set of the order. -/
noncomputable def orderComplexCoordinates (P : Type u)
    [PartialOrder P] [Fintype P] : C(|nerve P|,stdSimplex ℝ P) :=
  ((sSetTopAdj.homEquiv _ _).symm (orderComplexCoordinatesAdjoint P)).hom

end KIP126.Topology.SimplicialRealization
