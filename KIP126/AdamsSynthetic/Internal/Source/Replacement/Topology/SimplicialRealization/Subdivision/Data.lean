module

import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.Data.Finset.Max

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The maximum of a nonempty finite chain in a linear order. Inclusion
of chains makes this an order-preserving map. -/
noncomputable def finiteChainLastVertex (X : Type*) [LinearOrder X] :
    PartialOrder.NonemptyFiniteChains X →o X where
  toFun c := c.finset.max' c.nonempty
  monotone' a _b hab := Finset.max'_subset a.nonempty hab

/-- The last-vertex map on the actual barycentric subdivision of a
standard simplex. A flag of nonempty faces is sent to its sequence of
maximal vertices. -/
noncomputable def simplexSubdivisionLastVertex (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ SSet.stdSimplex.obj n :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom
    (finiteChainLastVertex (ULift.{u} (Fin (n.len+1))))) ≫
    (SSet.stdSimplex.isoNerve n.len).inv

/-- The maximum of the image of a finite chain is the image of its
maximum. Consequently last-vertex maps are natural for every simplex
map, including degeneracies. -/
noncomputable def simplexSubdivisionLastVertexNat :
    SimplexCategory.sd.{u} ⟶ SSet.stdSimplex where
  app := simplexSubdivisionLastVertex
  naturality {n m} f := by
    classical
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    change (Fin (d.unop.len+1) ⥤
      PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1)))) at s
    letI : DecidableEq (ULift.{u} (Fin (m.len+1))) := Classical.decEq _
    let g : ULift.{u} (Fin (n.len+1)) →o ULift.{u} (Fin (m.len+1)) := {
      toFun := fun x => ULift.up (f x.down)
      monotone' := fun _ _ h => f.toOrderHom.monotone h }
    apply SSet.stdSimplex.objEquiv.injective
    ext k
    change (((s.obj k).map g).finset.max' _).down.val =
      (f (((s.obj k).finset.max' _).down)).val
    simp only [PartialOrder.NonemptyFiniteChains.map]
    apply congrArg (fun x : ULift.{u} (Fin (m.len+1)) => x.down.val)
    apply (Finset.max'_eq_iff _ _ _).mpr
    constructor
    · exact Finset.mem_image.mpr ⟨_,(s.obj k).finset.max'_mem (s.obj k).nonempty,rfl⟩
    · intro b hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact g.monotone ((s.obj k).finset.le_max' a ha)

/-- The actual last-vertex natural transformation on all simplicial
sets, extended from the displayed maps of subdivided standard simplices. -/
noncomputable def subdivisionLastVertex : SSet.sd.{u} ⟶ 𝟭 SSet :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv
    (𝟭 SSet) simplexSubdivisionLastVertexNat

end KIP126.Topology.SimplicialRealization
