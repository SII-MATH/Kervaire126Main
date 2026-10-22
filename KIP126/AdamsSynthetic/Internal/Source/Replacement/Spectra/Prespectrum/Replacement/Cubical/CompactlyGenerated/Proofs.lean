module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/CompactlyGenerated/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Colimit.CompactlyGenerated.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.SmallObject
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual free-cell replacement stage has its original compactly
generated topology, by its genuine topological attachment universal property. -/
theorem cubicalReplacementStage_level_uCompactlyGeneratedSpace
    (X : Prespectrum.{u}) (k n : ℕ) :
    UCompactlyGeneratedSpace.{u} (((cellularStage cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X)) k).left).level n) := by
  induction k with
  | zero => exact inferInstanceAs (UCompactlyGeneratedSpace.{u} PUnit)
  | succ k ih =>
    letI : UCompactlyGeneratedSpace.{u} (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj
        (cellularStage cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X)) k).left) := ih
    letI (i : ℕ × ℕ) : UCompactlyGeneratedSpace.{u}
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (UCompactlyGeneratedSpace.{u} ((cubicalCellTarget i).level n))
    let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
      cubicalCellBoundary (cellularStage cubicalCellBoundary
        (Over.mk (zeroMap zeroPrespectrum X)) k).hom
    exact KIP126.Topology.uCompactlyGeneratedSpace_of_attachCells
      (attachCells_evaluation_forgetToTop c n)

/-- The original countable free-cell replacement has compactly generated
spaces in every level, without a separation or generation condition on X. -/
instance cubicalReplacementFunctor_level_uCompactlyGeneratedSpace
    (X : Prespectrum.{u}) (n : ℕ) :
    UCompactlyGeneratedSpace.{u} ((cubicalReplacementFunctor.obj X).level n) := by
  let F := cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  letI (k : ℕ) : UCompactlyGeneratedSpace.{u} ((F ⋙ E).obj k) :=
    cubicalReplacementStage_level_uCompactlyGeneratedSpace X k n
  exact KIP126.Topology.uCompactlyGeneratedSpace_of_isColimit (F ⋙ E)
    (E.mapCocone (colimit.cocone F)) (isColimitOfPreserves E (colimit.isColimit F))

end KIP126.AdamsSynthetic.Source.Prespectrum
