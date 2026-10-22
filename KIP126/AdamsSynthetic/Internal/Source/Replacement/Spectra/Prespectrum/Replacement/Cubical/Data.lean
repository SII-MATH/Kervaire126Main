module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cubical/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Zero.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Functorial.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.SmallObject

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual initial one-point prespectrum over the specified spectrum. -/
def cubicalInitialArrow : Prespectrum.{u} ⥤ Arrow Prespectrum.{u} where
  obj X := Arrow.mk (zeroMap zeroPrespectrum X)
  map {X Y} f := Arrow.homMk (𝟙 _) f (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact (f.point n).symm)
  map_id X := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply Arrow.hom_ext <;> rfl

/-- A countable actual free-cubical attachment replacement of a prespectrum,
functorial because every commuting square is attached at each stage. -/
noncomputable def cubicalReplacementFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj X := cellularReplacement cubicalCellBoundary
    (Over.mk (zeroMap zeroPrespectrum X))
  map f := cellularReplacementMap cubicalCellBoundary (cubicalInitialArrow.map f)
  map_id X := by
    rw [cubicalInitialArrow.map_id]
    exact cellularReplacementMap_id _ _
  map_comp f g := by
    rw [cubicalInitialArrow.map_comp]
    exact cellularReplacementMap_comp _ _ _

/-- The actual comparison of the functorial free-cubical replacement to the
original prespectrum; its naturality is strict. -/
noncomputable def cubicalReplacementComparison : cubicalReplacementFunctor.{u} ⟶ 𝟭 _ where
  app X := cellularComparison cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))
  naturality _ _ f := cellularReplacementMap_comparison cubicalCellBoundary
    (cubicalInitialArrow.map f)

end KIP126.AdamsSynthetic.Source.Prespectrum
