module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/Geometry/Refinement/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Geometry.Attachment.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CategoryTheory.CellAttachment.Refinement.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory HomotopicalAlgebra KIP126.Topology.HomotopyLifting
open KIP126.Topology.SmallObject

universe u

set_option backward.isDefEq.respectTransparency false

/-- An arbitrary batch of original free cubical cells is an actual batch
of ordinary cube cells at every level, with the same original level map. -/
theorem cubicalAttachCells_level_attachCells {X Y : Prespectrum.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} cubicalCellBoundary f) (n : ℕ) :
    Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
      (TopCat.ofHom (f.level n))) := by
  classical
  exact KIP126.Foundation.CellAttachment.nonempty_refinement
    (attachCells_evaluation_forgetToTop c n)
    (fun i => (cubicalCellBoundary_level_attachCells i n).some)

/-- Every transition in the actual free cubical replacement process has
an ordinary cubical attachment presentation at each specified level. -/
theorem cubicalCellularStageMap_level_attachCells
    {S : Prespectrum.{u}} (X : Over S) (k n : ℕ) :
    Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
      (TopCat.ofHom ((cellularStageMap cubicalCellBoundary X k).level n))) :=
  cubicalAttachCells_level_attachCells
    (CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
      cubicalCellBoundary (cellularStage cubicalCellBoundary X k).hom) n

end KIP126.AdamsSynthetic.Source.Prespectrum
