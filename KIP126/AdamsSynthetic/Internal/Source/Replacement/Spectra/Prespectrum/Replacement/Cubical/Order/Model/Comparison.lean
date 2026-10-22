module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/Order/Model/Comparison.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Invariance.Proofs

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

universe u

/-- The specified realization comparison with its proved original
basepoint equation, as a morphism of actual based spaces. -/
noncomputable def cubicalReplacementBasedRealizedComparison (X : Prespectrum.{u}) (n : ℕ) :
    cubicalReplacementRealizedModel X n ⟶ (cubicalReplacementFunctor.obj X).level n where
  map := (cubicalReplacementRealizedComparison X n).hom
  point := cubicalReplacementRealizedComparison_point X n

end KIP126.AdamsSynthetic.Source.Prespectrum

end

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits Simplicial
open KIP126.Topology.SimplicialRealization KIP126.Topology.SequentialColimit

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified map from the actual simplicial CW model to the original
replacement level is an actual homotopy equivalence, with that exact forward
map. No CW type or compatible stage homotopies are supplied as assumptions. -/
theorem cubicalReplacementRealizedComparison_homotopyEquiv (X : Prespectrum.{u}) (n : ℕ) :
    ∃ E : ContinuousMap.HomotopyEquiv (cubicalReplacementRealizedModel X n)
        ((cubicalReplacementFunctor.obj X).level n),
      E.toFun = (cubicalReplacementBasedRealizedComparison X n).map := by
  let G := cubicalReplacementLevelSequence X n
  let hc := cubicalReplacementLevelSequence_attachCells X n
  let M := cubicalReplacementInitialOrderModel X n
  let K := cubicalReplacementSimplicialSequence X n
  let η := cubicalOrderSequenceComparison G hc M
  exact exists_colimit_homotopyEquiv_of_level η
    (fun k => (cubicalOrderStageModel G hc M k).equivalence) (fun _ => rfl)
    (SSet.toTop.mapCocone (colimit.cocone K)) (cubicalReplacementLevelCocone X n)
    (isColimitOfPreserves SSet.toTop (colimit.isColimit K))
    (cubicalReplacementLevelCocone_isColimit X n).some
    (fun k => cubicalOrderRealizationSequence_map_hasHomotopyExtension G hc M (Nat.le_succ k))
    (fun k => cubicalOrderRealizationSequence_map_isClosedEmbedding G hc M (Nat.le_succ k))
    (fun k => (cubicalReplacementLevelSequence_closedHEP X n k).2)
    (fun k => (cubicalReplacementLevelSequence_closedHEP X n k).1)
    (cubicalReplacementRealizedComparison X n)
    (fun k => cubicalReplacementRealizedComparison_stage X n k)

end KIP126.AdamsSynthetic.Source.Prespectrum

end
