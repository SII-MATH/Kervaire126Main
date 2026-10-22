module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Free/CompactFactor/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Evaluation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Connected.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Compact.Proofs
import Mathlib.CategoryTheory.Filtered.Connected

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- A strict map out of the actual free prespectrum on a compact based
space factors through a finite stage of a levelwise closed T1 sequence.
The factorization is strict and based, not merely a homotopy factorization. -/
theorem free_map_factor_sequential_colimit
    (F : ℕ ⥤ Prespectrum.{u}) (c : Cocone F) (hc : IsColimit c)
    (n : ℕ) [∀ k, T1Space ((F.obj k).level n)]
    (hF : ∀ k, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n))
    (A : BasedSpace.{u}) [CompactSpace A] (f : free n A ⟶ c.pt) :
    ∃ (k : ℕ) (g : free n A ⟶ F.obj k), g ≫ c.ι.app k = f := by
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  letI : PreservesColimit F E := by
    dsimp only [E]
    infer_instance
  let D := F ⋙ E
  let d := E.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves E hc
  letI (k : ℕ) : T1Space (D.obj k) := inferInstanceAs (T1Space ((F.obj k).level n))
  have hD : ∀ k, IsClosedEmbedding (D.map (homOfLE (Nat.le_succ k))) := hF
  obtain ⟨k,g,hg⟩ := KIP126.Topology.continuousMap_factor_nat_colimit D d hd hD
    (freeEvaluation n A c.pt f).map
  have hι := (KIP126.Topology.isClosedEmbedding_nat_colimit D d hd hD k).injective
  have gp : g A.point = ((F.obj k).level n).point := by
    apply hι
    exact (hg A.point).trans ((freeEvaluation n A c.pt f).point.trans
      ((c.ι.app k).point n).symm)
  let g' : A ⟶ (F.obj k).level n := ⟨g,gp⟩
  refine ⟨k,(freeEvaluation n A (F.obj k)).symm g',?_⟩
  apply (freeEvaluation n A c.pt).injective
  rw [freeEvaluation_natural,Equiv.apply_symm_apply]
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  exact hg

end KIP126.AdamsSynthetic.Source.Prespectrum
