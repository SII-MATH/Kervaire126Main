module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CWComplex.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.ClosedEmbedding.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.Hausdorff.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The identification of cells with nondegenerate simplices preserves
cell dimension. -/
@[simp] theorem cwComplexCellsEquiv_dim (X : SSet.{u}) (c : (cwComplex X).Cells) :
    (cwComplexCellsEquiv X c).dim = c.j := rfl

/-- A finite simplicial set gives a CW realization with finitely many cells. -/
theorem finite_cwComplex_cells (X : SSet.{u}) [X.Finite] :
    Finite (cwComplex X).Cells := Finite.of_equiv X.N (cwComplexCellsEquiv X).symm

/-- Finite simplices in one degree imply finitely many cells attached at
that actual stage of the realized CW filtration. -/
theorem finite_cwComplex_stage_cells (X : SSet.{u}) (n : ℕ)
    [Finite (X.obj (op ⦋n⦌))] (hn : ¬ IsMax n) :
    Finite ((cwComplex X).attachCells n hn).ι := by
  change Finite (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n)
  exact Finite.of_injective (fun c => c.simplex) (by intro a b h; cases a; cases b; cases h; rfl)

/-- Degreewise finite simplicial sets have genuine finite CW skeleta. -/
theorem finite_cwComplex_skeleton_cells (X : SSet.{u}) (n : ℕ)
    (hX : ∀ d : ℕ, Finite (X.obj (op ⦋d⦌))) :
    Finite (cwComplex (X.skeleton n).toSSet).Cells := by
  letI := finite_skeleton X n hX
  exact finite_cwComplex_cells _

/-- Each stage of the actual realized CW filtration is compact when
there are finitely many simplices in every degree. -/
theorem compactSpace_cwComplex_stage (X : SSet.{u}) (n : ℕ)
    (hX : ∀ d : ℕ, Finite (X.obj (op ⦋d⦌))) :
    CompactSpace ((cwComplex X).F.obj n) := by
  letI := compactSpace_skeleton X n hX
  exact (TopCat.homeoOfIso (cwComplexSkeletonIso X n)).symm.compactSpace

/-- The genuine Euclidean disk boundary inclusion is a closed embedding. -/
theorem diskBoundaryInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n) :=
  KIP126.Topology.diskBoundaryInclusion_isClosedEmbedding n

/-- Actual successive realization skeleta are closed embedded subspaces,
as follows from their proved boundary attachments. -/
theorem cwComplex_stage_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding ((cwComplex X).F.map (homOfLE (Nat.le_succ n))) :=
  KIP126.Topology.isClosedEmbedding_of_attachCells
    ((cwComplex X).attachCells n (by simp))
    (fun _ => diskBoundaryInclusion_isClosedEmbedding n)

/-- The actual geometric realization of every simplicial set is Hausdorff. -/
theorem realization_t2Space (X : SSet.{u}) : T2Space |X| :=
  KIP126.Topology.cwComplex_t2Space (cwComplex X)

end KIP126.Topology.SimplicialRealization
