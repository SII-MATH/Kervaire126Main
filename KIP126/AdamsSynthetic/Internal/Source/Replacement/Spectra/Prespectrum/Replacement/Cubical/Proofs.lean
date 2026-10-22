module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Evaluation.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Lifting.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.CompactFactor.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Separation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Separation.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each genuine free-cubical attachment stage is closed embedded at
every actual level. -/
theorem cubicalReplacementStageMap_level_isClosedEmbedding
    (X : Prespectrum.{u}) (k n : ℕ) :
    IsClosedEmbedding ((cellularStageMap cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X)) k).level n) := by
  let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
    cubicalCellBoundary (cellularStage cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X)) k).hom
  exact KIP126.Topology.isClosedEmbedding_of_attachCells
    (attachCells_evaluation_forgetToTop c n)
    (fun i => cubicalCellBoundary_level_isClosedEmbedding i n)

/-- All levels of all actual stages are T1, starting from the genuine
one-point prespectrum and attaching compact Hausdorff free cells. -/
theorem cubicalReplacementStage_level_t1Space (X : Prespectrum.{u}) (k n : ℕ) :
    T1Space (((cellularStage cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X)) k).left).level n) := by
  induction k with
  | zero => exact inferInstanceAs (T1Space PUnit)
  | succ k ih =>
    letI : T1Space (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj
        (cellularStage cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X)) k).left) := ih
    letI (i : ℕ × ℕ) : NormalSpace
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (NormalSpace ((cubicalCellTarget i).level n))
    letI (i : ℕ × ℕ) : T1Space
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (T1Space ((cubicalCellTarget i).level n))
    let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
      cubicalCellBoundary (cellularStage cubicalCellBoundary
        (Over.mk (zeroMap zeroPrespectrum X)) k).hom
    exact KIP126.Topology.t1Space_of_attachCells
      (attachCells_evaluation_forgetToTop c n)
      (fun i => cubicalCellBoundary_level_isClosedEmbedding i n)

/-- The actual functorial prespectrum replacement has T1 spaces in every
level, without any separation assumption on the original spectrum. -/
instance cubicalReplacementFunctor_level_t1Space (X : Prespectrum.{u}) (n : ℕ) :
    T1Space ((cubicalReplacementFunctor.obj X).level n) := by
  let F := cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  letI (k : ℕ) : T1Space ((F ⋙ E).obj k) :=
    cubicalReplacementStage_level_t1Space X k n
  have hF : ∀ k, IsClosedEmbedding ((F ⋙ E).map (homOfLE (Nat.le_succ k))) := by
    intro k
    change IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n)
    dsimp only [F,cellularSequence]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact cubicalReplacementStageMap_level_isClosedEmbedding X k n
  exact KIP126.Topology.t1Space_nat_colimit (F ⋙ E) (E.mapCocone (colimit.cocone F))
    (isColimitOfPreserves E (colimit.isColimit F)) hF

/-- Every free cubical boundary lifting problem in the genuine countable
replacement factors through a finite stage and is solved in the next one. -/
theorem cubicalReplacementComparison_hasLiftingProperty (X : Prespectrum.{u}) (i : ℕ × ℕ) :
    HasLiftingProperty (cubicalCellBoundary i) (cubicalReplacementComparison.app X) := by
  constructor
  intro t b sq
  let F := cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))
  letI (k : ℕ) : T1Space ((F.obj k).level i.1) :=
    cubicalReplacementStage_level_t1Space X k i.1
  have hF : ∀ k, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level i.1) := by
    intro k
    dsimp only [F,cellularSequence]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact cubicalReplacementStageMap_level_isClosedEmbedding X k i.1
  obtain ⟨k,g,hg⟩ := free_map_factor_sequential_colimit F (colimit.cocone F)
    (colimit.isColimit F) i.1 hF (BasedSpace.adjoinPoint (cubeBoundaryObject i.2)) t
  obtain ⟨l,hl,hπ⟩ := cellularComparison_extension cubicalCellBoundary
    (Over.mk (zeroMap zeroPrespectrum X)) i t b sq.w k g hg
  exact CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := hπ }

/-- The actual natural comparison lifts every full cube-boundary square
at every level. -/
theorem cubicalReplacementComparison_level_hasCubeBoundaryLifting
    (X : Prespectrum.{u}) (n : ℕ) :
    HasCubeBoundaryLifting ((cubicalReplacementComparison.app X).level n) :=
  hasCubeBoundaryLifting_of_cubicalCellBoundary _
    (cubicalReplacementComparison_hasLiftingProperty X) n

/-- The natural comparison of the actual replacement induces bijections
on every based cubical homotopy set at every level, including degree zero. -/
theorem cubicalReplacementComparison_level_homotopy_bijective
    (X : Prespectrum.{u}) (n d : ℕ) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap
      ((cubicalReplacementComparison.app X).level n)
      ((cubicalReplacementFunctor.obj X).level n).point (X.level n).point
      ((cubicalReplacementComparison.app X).point n) d) :=
  (cubicalReplacementComparison_level_hasCubeBoundaryLifting X n).continuousHomotopyMap_bijective
    _ _ _ d

/-- The strictly natural comparison from the actual T1 replacement is
an actual stable equivalence. -/
theorem cubicalReplacementComparison_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (cubicalReplacementComparison.app X) :=
  stableEquivalence_of_cubicalCellBoundary_lifting _
    (cubicalReplacementComparison_hasLiftingProperty X)

end KIP126.AdamsSynthetic.Source.Prespectrum
