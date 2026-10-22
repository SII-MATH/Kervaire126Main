module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/Suspension/Cell/Iterate/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell.Pushout.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Inclusion

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory KIP126.Topology.HomotopyLifting

universe u

/-- Every finite iterate of actual reduced suspension takes an actual
single cubical attachment to a single cubical attachment of shifted dimension. -/
theorem iterateSuspensionMap_exists_cube_attachment (n : ℕ) {A B : BasedSpace.{u}}
    (a : cubeBoundaryObject n ⟶ A.space) (c : cubeObject n ⟶ B.space)
    (f : A ⟶ B) (h : IsPushout (cubeBoundaryInclusion n) a c (TopCat.ofHom f.map))
    (k : ℕ) :
    ∃ (a' : cubeBoundaryObject (n+k) ⟶ (A.iterateSuspension k).space)
      (c' : cubeObject (n+k) ⟶ (B.iterateSuspension k).space),
      IsPushout (cubeBoundaryInclusion (n+k)) a' c'
        (TopCat.ofHom (iterateSuspensionMap f k).map) := by
  induction k with
  | zero => exact ⟨a,c,h⟩
  | succ k ih =>
    obtain ⟨a',c',hh⟩ := ih
    exact ⟨suspensionCellBoundary (n+k) _ a',
      suspensionCellCharacteristic (n+k) _ c',
      suspendMap_isPushout_of_cube_attachment (n+k) a' c' (iterateSuspensionMap f k) hh⟩

/-- The original iterated suspension of a cubical boundary with disjoint
basepoint is itself an actual ordinary cubical attachment. -/
theorem iterateSuspensionAdjoinPointCube_exists_attachment (n k : ℕ) :
    ∃ (a : cubeBoundaryObject.{u} (n+k) ⟶
        ((adjoinPoint (cubeBoundaryObject n)).iterateSuspension k).space)
      (c : cubeObject.{u} (n+k) ⟶
        ((adjoinPoint (cubeObject n)).iterateSuspension k).space),
      IsPushout (cubeBoundaryInclusion (n+k)) a c
        (TopCat.ofHom (iterateSuspensionMap
          (adjoinPointMap (cubeBoundaryInclusion n)) k).map) :=
  iterateSuspensionMap_exists_cube_attachment n
    (adjoinPointInclusion (cubeBoundaryObject n)) (adjoinPointInclusion (cubeObject n))
    (adjoinPointMap (cubeBoundaryInclusion n))
    (adjoinPointMap_isPushout (cubeBoundaryInclusion n)) k

end KIP126.AdamsSynthetic.Source.BasedSpace
