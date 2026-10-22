module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/HomotopyExtension/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.HomotopyExtension.AdjoinPoint.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.HomotopyExtension.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Extension.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory _root_.Topology
open KIP126.Topology.HomotopyLifting KIP126.Topology.HomotopyExtension
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual free prespectrum on a compact Hausdorff based
homotopy-extension injection has that property at every level. -/
theorem freeMap_level_hasHomotopyExtension (n : ℕ) {A B : BasedSpace.{u}}
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (f : A ⟶ B) (hf : Function.Injective f.map)
    (hH : HasHomotopyExtension (TopCat.ofHom f.map)) (k : ℕ) :
    HasHomotopyExtension (TopCat.ofHom ((freeMap n f).level k)) := by
  induction n generalizing k with
  | zero =>
    rw [freeMap_zero]
    exact BasedSpace.iterateSuspensionMap_hasHomotopyExtension f hf hH k
  | succ n ih =>
    rw [freeMap_succ]
    have heq {X X' Y Y' : Prespectrum.{u}} (hX : X = X') (hY : Y' = Y)
        (g : X' ⟶ Y') (k : ℕ)
        (hg : HasHomotopyExtension (TopCat.ofHom (g.level k))) :
        HasHomotopyExtension
          (TopCat.ofHom ((eqToHom hX ≫ g ≫ eqToHom hY).level k)) := by
      subst X'
      subst Y'
      exact hg
    apply heq
    cases k with
    | zero =>
      intro Z g p hp
      exact ⟨p, hp, fun _ _ => rfl⟩
    | succ k => exact ih k

/-- Every actual free cubical boundary used by prespectrum replacement
has full homotopy extension at every level, including its iterated
reduced-suspension levels. -/
theorem cubicalCellBoundary_level_hasHomotopyExtension (i : ℕ × ℕ) (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom ((cubicalCellBoundary.{u} i).level n)) := by
  letI : CompactSpace (cubeObject.{u} i.2) :=
    inferInstanceAs (CompactSpace (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (Fin i.2 → I)))
  letI : T2Space (cubeBoundaryObject.{u} i.2) :=
    inferInstanceAs (T2Space (ULift.{u} (↥(_root_.Cube.boundary (Fin i.2)))))
  exact freeMap_level_hasHomotopyExtension i.1 _
    (BasedSpace.adjoinPointMap_injective _
      (cubeBoundaryInclusion_isClosedEmbedding i.2).injective)
    (BasedSpace.adjoinPointMap_hasHomotopyExtension _
      (cubeBoundaryInclusion_hasHomotopyExtension i.2)) n

end KIP126.AdamsSynthetic.Source.Prespectrum
