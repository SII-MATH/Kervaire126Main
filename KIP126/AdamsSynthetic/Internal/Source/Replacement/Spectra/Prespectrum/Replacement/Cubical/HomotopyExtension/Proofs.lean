module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/HomotopyExtension/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Cells.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyExtension

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each actual free-cubical attachment stage inclusion, starting from
any specified strict map, has full homotopy extension at every level. -/
theorem cubicalCellularStageMap_level_hasHomotopyExtension
    {S : Prespectrum.{u}} (X : Over S) (k n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom
      ((cellularStageMap cubicalCellBoundary X k).level n)) := by
  let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
    cubicalCellBoundary (cellularStage cubicalCellBoundary X k).hom
  exact hasHomotopyExtension_of_attachCells (attachCells_evaluation_forgetToTop c n)
    (fun i => cubicalCellBoundary_level_hasHomotopyExtension i n)

/-- The initial space of any actual free-cubical attachment sequence
includes into its countable colimit with full level homotopy extension. -/
theorem cubicalCellularInitialInclusion_level_hasHomotopyExtension
    {S : Prespectrum.{u}} (X : Over S) (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom ((colimit.ι
      (cellularSequence cubicalCellBoundary X) 0).level n)) := by
  let F := cellularSequence cubicalCellBoundary X
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  apply (hasHomotopyExtension_iff_lifting _).mpr
  intro Z
  apply HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
    (isColimitOfPreserves E (colimit.isColimit F))
  intro k hk
  change HasLiftingProperty (E.map (F.map (homOfLE (Nat.le_succ k)))) _
  dsimp only [F, cellularSequence]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact (hasHomotopyExtension_iff_lifting _).mp
    (cubicalCellularStageMap_level_hasHomotopyExtension X k n) Z

/-- Each actual free-cubical replacement stage has full level homotopy
extension, with no condition on the spectrum being replaced. -/
theorem cubicalReplacementStageMap_level_hasHomotopyExtension
    (X : Prespectrum.{u}) (k n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom ((cellularStageMap cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X)) k).level n)) :=
  cubicalCellularStageMap_level_hasHomotopyExtension _ k n

/-- The actual initial one-point level includes into the countable
replacement with full homotopy extension. -/
theorem cubicalReplacementInitialInclusion_level_hasHomotopyExtension
    (X : Prespectrum.{u}) (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom ((colimit.ι
      (cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))) 0).level n)) :=
  cubicalCellularInitialInclusion_level_hasHomotopyExtension _ n

end KIP126.AdamsSynthetic.Source.Prespectrum
