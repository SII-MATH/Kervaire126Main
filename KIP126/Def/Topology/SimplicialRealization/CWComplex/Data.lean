module

public import KIP126.Def.Topology.SimplicialRealization.DiskPair.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomotopicalAlgebra

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual simplex filtration, expressed using Euclidean disk attachments.
The arrow comparison preserves both boundary inclusions and attaching maps. -/
noncomputable def diskCellComplex (X : SSet.{u}) :
    TopCat.RelativeCWComplex (SSet.toTop.map (SSet.Subcomplex.ι (⊥ : X.Subcomplex))) where
  toTransfiniteCompositionOfShape := (cellComplex X).toTransfiniteCompositionOfShape
  attachCells n hn :=
    ((cellComplex X).attachCells n hn).reindexCellTypes
      (TopCat.RelativeCWComplex.basicCell n) (fun _ => Unit.unit)
      (fun _ => Classical.choice (nonempty_boundary_realization_disk_arrow_iso n))

/-- Geometric realization carries its genuine skeletal CW structure, with
one Euclidean cell for each nondegenerate simplex. -/
noncomputable def cwComplex (X : SSet.{u}) : TopCat.CWComplex (SSet.toTop.obj X) := by
  let c := diskCellComplex X
  let h0 := (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj SSet.toTop
  let E : Arrow.mk (SSet.toTop.map (SSet.Subcomplex.ι (⊥ : X.Subcomplex))) ≅
      Arrow.mk (initial.to (SSet.toTop.obj X)) :=
    Arrow.isoMk (h0.uniqueUpToIso (initialIsInitial)) (Iso.refl _) (h0.hom_ext _ _)
  exact {
    toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofArrowIso E
    attachCells := c.attachCells }

end KIP126.Topology.SimplicialRealization
