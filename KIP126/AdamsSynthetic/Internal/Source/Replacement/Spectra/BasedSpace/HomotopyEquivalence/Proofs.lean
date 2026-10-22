module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/HomotopyEquivalence/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Relative.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Under.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace
open CategoryTheory _root_.Topology
open KIP126.Topology.HomotopyExtension
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual specified point inclusion of a well-based space is closed embedded. -/
theorem IsWellBased.pointInclusion_isClosedEmbedding {X : BasedSpace.{u}} (hX : X.IsWellBased) :
    IsClosedEmbedding (toUnder.obj X).hom := by
  refine ⟨IsEmbedding.of_subsingleton _,?_⟩
  have hr : Set.range (toUnder.obj X).hom = {X.point} := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; rfl
    · rintro rfl; exact ⟨PUnit.unit,rfl⟩
  rw [hr]
  exact hX.1

/-- The actual specified point inclusion has full homotopy extension. -/
theorem IsWellBased.pointInclusion_hasHomotopyExtension {X : BasedSpace.{u}} (hX : X.IsWellBased) :
    HasHomotopyExtension (toUnder.obj X).hom := by
  intro Y f p hp
  let q : C(I,Y) := p.comp ((ContinuousMap.const I PUnit.unit).prodMk (ContinuousMap.id I))
  obtain ⟨H,hH,hHpt⟩ := hX.2 Y f q (hp PUnit.unit)
  refine ⟨H,hH,?_⟩
  intro z t
  cases z
  exact hHpt t

/-- A based map between actual well-based spaces which is an ordinary
homotopy equivalence has a based inverse and both homotopies fixed at the specified points. -/
theorem exists_based_inverse_of_homotopyEquiv
    {X Y : BasedSpace.{u}} (hX : X.IsWellBased) (hY : Y.IsWellBased)
    (f : X ⟶ Y) (e : ContinuousMap.HomotopyEquiv X Y) (he : e.toFun = f.map) :
    ∃ g : Y ⟶ X,
      (g.map.comp f.map).HomotopicRel (ContinuousMap.id X) {X.point} ∧
      (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point} := by
  have hf : (toUnder.obj X).hom ≫ TopCat.ofHom f.map = (toUnder.obj Y).hom := by
    ext z
    exact f.point
  obtain ⟨g,hg,hL,hR⟩ := exists_relative_inverse_of_homotopyEquiv
    (toUnder.obj X).hom (toUnder.obj Y).hom
    hX.pointInclusion_hasHomotopyExtension hX.pointInclusion_isClosedEmbedding
    hY.pointInclusion_hasHomotopyExtension (TopCat.ofHom f.map) hf e he
  have hXr : Set.range (toUnder.obj X).hom = {X.point} := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; rfl
    · rintro rfl; exact ⟨PUnit.unit,rfl⟩
  have hYr : Set.range (toUnder.obj Y).hom = {Y.point} := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; rfl
    · rintro rfl; exact ⟨PUnit.unit,rfl⟩
  exact ⟨⟨g,hg PUnit.unit⟩,hXr ▸ hL,hYr ▸ hR⟩

end KIP126.AdamsSynthetic.Source.BasedSpace

