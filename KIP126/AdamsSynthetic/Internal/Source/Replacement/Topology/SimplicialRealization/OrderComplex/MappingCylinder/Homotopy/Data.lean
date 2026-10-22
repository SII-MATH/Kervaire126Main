module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular.Cylinder.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite MonoidalCategory

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Pointwise comparable order maps act on the actual simplicial prism
by switching once from the lower map to the upper map. -/
def orderMapCylinderSimplex (f g : P →o Q) (hfg : ∀ p, f p ≤ g p)
    {d : SimplexCategoryᵒᵖ} (s : (nerve P).obj d) (t : (Δ[1] : SSet.{u}).obj d) :
    Fin (d.unop.len+1) →o Q where
  toFun k := if (SSet.stdSimplex.objEquiv t).toOrderHom k = 0 then f (s.obj k) else g (s.obj k)
  monotone' := by
    intro a b hab
    have ht := (SSet.stdSimplex.objEquiv t).toOrderHom.monotone hab
    have hs := s.monotone hab
    dsimp only
    split_ifs with ha hb hb
    · exact f.monotone hs
    · exact (f.monotone hs).trans (hfg (s.obj b))
    · exact (ha (le_antisymm (hb ▸ ht) (Fin.zero_le _))).elim
    · exact g.monotone hs

/-- The actual simplicial cylinder map determined by a pointwise order inequality. -/
def orderMapCylinder (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) :
    nerve P ⊗ Δ[1] ⟶ nerve Q where
  app d := TypeCat.ofHom fun z => (orderMapCylinderSimplex f g hfg z.1 z.2).monotone.functor
  naturality {d e} a := by
    apply ConcreteCategory.hom_ext
    intro z
    exact CategoryTheory.Functor.ext (fun k => rfl)

end KIP126.Topology.SimplicialRealization
