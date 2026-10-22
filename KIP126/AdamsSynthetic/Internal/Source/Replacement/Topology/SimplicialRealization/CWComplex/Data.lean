module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.DiskPair.Proofs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] section

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

/-- The cells of the constructed CW structure are precisely the actual
nondegenerate simplices; dimensions and indexing are unchanged by the disk
pair homeomorphisms. -/
noncomputable def cwComplexCellsEquiv (X : SSet.{u}) : (cwComplex X).Cells ≃ X.N where
  toFun c := SSet.N.mk _ c.k.nonDegenerate
  invFun s :=
    { j := s.dim
      hj := by simp
      k := { simplex := s.simplex, nonDegenerate := s.nonDegenerate, notMem := by simp } }
  left_inv := fun ⟨j,hj,k⟩ => by cases k; rfl
  right_inv := fun s => by cases s; rfl

/-- Each stage of the constructed CW filtration is the realization of
the genuine simplicial skeleton, generated in dimensions below `n`. -/
noncomputable def cwComplexSkeletonIso (X : SSet.{u}) (n : ℕ) :
    (cwComplex X).F.obj n ≅ skeleton X n :=
  SSet.toTop.mapIso (SSet.Subcomplex.eqToIso (by simp [SSet.skeletonOfMono]))

end KIP126.Topology.SimplicialRealization
