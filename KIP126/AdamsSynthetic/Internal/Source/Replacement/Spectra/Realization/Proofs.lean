module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Realization/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Realization.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CompactlyGenerated.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Relative.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Charts.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Opposite Simplicial
open KIP126.Topology.SimplicialRealization

universe u

theorem basedRealization_point (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    SSet.toTop.map (SSet.const v : Δ[0] ⟶ K) default = (basedRealization K v).point :=
  realization_vertex_eq_unit K v

/-- Each vertex in the actual realization is a closed based cofibration. -/
theorem basedRealization_isWellBased (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    (basedRealization K v).IsWellBased := by
  constructor
  · rw [← basedRealization_point K v]
    exact vertex_isClosed K v
  · intro Y f p hp
    obtain ⟨H,hH0,hHi⟩ := vertex_homotopy_extension K v Y f p (by
      rw [basedRealization_point K v]
      exact hp)
    rw [basedRealization_point K v] at hHi
    exact ⟨H,hH0,hHi⟩

/-- The realization itself is a based CW model, with identity comparisons. -/
theorem basedRealization_hasCWType (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    (basedRealization K v).HasCWType := by
  refine ⟨basedRealization K v,realization_t2Space K,
    realization_nonempty_classicalCWComplex K,basedRealization_isWellBased K v,
    𝟙 _,𝟙 _,?_,?_⟩
  all_goals exact ContinuousMap.HomotopicRel.refl _

/-- The actual realization at any chosen vertex satisfies every good-space
condition; no finiteness or Kan assumption is needed. -/
theorem basedRealization_isGood (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    (basedRealization K v).IsGood :=
  ⟨realization_uCompactlyGeneratedSpace K,basedRealization_isWellBased K v,
    basedRealization_hasCWType K v⟩

end KIP126.AdamsSynthetic.Source
