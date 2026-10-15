module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cells.Geometry.Proofs
public import KIP126.Def.CategoryTheory.CellAttachment.Basic.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cells.Evaluation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory HomotopicalAlgebra KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual level of an original free cubical boundary generator is
an ordinary cube-cell attachment. Below its free level the family is empty;
at and above it there is one cell of the shifted dimension. -/
theorem cubicalCellBoundary_level_attachCells (i : ℕ × ℕ) (k : ℕ) :
    Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
      (((evaluationFunctor k) ⋙ BasedSpace.forgetToTop).map (cubicalCellBoundary i))) := by
  change Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
    (TopCat.ofHom ((freeMap i.1
      (BasedSpace.adjoinPointMap (cubeBoundaryInclusion i.2))).level k)))
  by_cases hk : i.1 ≤ k
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨a,c,h⟩ := freeCubicalBoundary_level_exists_attachment.{u} i.1 i.2 d
    exact KIP126.Foundation.CellAttachment.nonempty_of_isPushout
      cubeBoundaryInclusion (i.2+d) a c _ h.flip
  · letI := freeMap_level_isIso_below i.1
      (BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{u} i.2)) k (by omega)
    exact KIP126.Foundation.CellAttachment.nonempty_of_isIso cubeBoundaryInclusion
      (TopCat.ofHom ((freeMap i.1
        (BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{u} i.2))).level k))

end KIP126.StableHomotopy.Spectra.Prespectrum
