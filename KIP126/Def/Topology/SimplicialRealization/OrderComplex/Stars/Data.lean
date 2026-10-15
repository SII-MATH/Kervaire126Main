module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

/-- The open star of an actual vertex consists of realized points with
strictly positive coordinate at that vertex. -/
def orderOpenStar (P : Type u) [PartialOrder P] [Fintype P] (p : P) :
    Set |nerve P| := {x | 0 < orderComplexCoordinates P x p}

/-- The common open star of a finite set of actual vertices. -/
def orderOpenStarIntersection (P : Type u) [PartialOrder P] [Fintype P]
    (s : Finset P) : Set |nerve P| := {x | ∀ p ∈ s, x ∈ orderOpenStar P p}

/-- The actual realized vertex, represented by its constant zero simplex. -/
noncomputable def orderVertex (P : Type u) [PartialOrder P] (p : P) : |nerve P| :=
  simplexPoint (nerve P) (a := op ⦋0⦌)
    (OrderHom.const (Fin 1) p).monotone.functor (stdSimplex.vertex 0)

end KIP126.Topology.SimplicialRealization
