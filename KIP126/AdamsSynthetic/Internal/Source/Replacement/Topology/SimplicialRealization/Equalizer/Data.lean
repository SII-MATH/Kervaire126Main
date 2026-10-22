module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
set_option backward.isDefEq.respectTransparency false

/-- The characteristic map of a simplex in the geometric realization. -/
noncomputable def simplexPoint (A : SSet.{u}) {a : SimplexCategoryᵒᵖ}
    (x : A.obj a) : C(stdSimplex ℝ (Fin (a.unop.len + 1)), |A|) :=
  (SSet.toTop.obj A).toSSetObjEquiv a ((sSetTopAdj.unit.app A).app a x)

/-- The literal subcomplex on which two simplicial maps agree. -/
def equalitySubcomplex {X Y : SSet.{u}} (f g : X ⟶ Y) : X.Subcomplex where
  obj a := {x | f.app a x = g.app a x}
  map i := by
    intro x hx
    exact (NatTrans.naturality_apply f i x).trans
      ((congrArg (Y.map i) hx).trans (NatTrans.naturality_apply g i x).symm)

/-- The comparison to the literal topological equality locus. -/
noncomputable def equalityComparison {X Y : SSet.{u}} (f g : X ⟶ Y) :
    C(|(equalitySubcomplex f g).toSSet|,
      {x : |X| // SSet.toTop.map f x = SSet.toTop.map g x}) where
  toFun x := ⟨SSet.toTop.map (equalitySubcomplex f g).ι x,
    by
      have he : (equalitySubcomplex f g).ι ≫ f = (equalitySubcomplex f g).ι ≫ g := by
        ext a z
        exact z.property
      have h := congrArg SSet.toTop.map he
      rw [Functor.map_comp, Functor.map_comp] at h
      exact ConcreteCategory.congr_hom h x⟩
  continuous_toFun := (SSet.toTop.map (equalitySubcomplex f g).ι).hom.continuous.subtype_mk _


end KIP126.Topology.SimplicialRealization
