module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/Geometry/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell.Iterate.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.Geometry.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- At and above its generating level, the original free cubical generator
is an actual ordinary single-cell attachment of the expected dimension. -/
theorem freeCubicalBoundary_level_exists_attachment (r n k : ℕ) :
    ∃ (a : cubeBoundaryObject.{u} (n+k) ⟶
        ((free r (BasedSpace.adjoinPoint (cubeBoundaryObject n))).level (r+k)).space)
      (c : cubeObject.{u} (n+k) ⟶
        ((free r (BasedSpace.adjoinPoint (cubeObject n))).level (r+k)).space),
      IsPushout (cubeBoundaryInclusion (n+k)) a c
        (TopCat.ofHom ((freeMap r
          (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n))).level (r+k))) := by
  induction r with
  | zero =>
    rw [freeMap_zero, Nat.zero_add]
    exact BasedSpace.iterateSuspensionAdjoinPointCube_exists_attachment n k
  | succ r ih =>
    rw [freeMap_succ]
    have transport {X X' Y Y' : Prespectrum.{u}} (hX : X = X') (hY : Y' = Y)
        (g : X' ⟶ Y') (l d : ℕ)
        (hh : ∃ (a : cubeBoundaryObject d ⟶ (X'.level l).space)
          (c : cubeObject d ⟶ (Y'.level l).space),
          IsPushout (cubeBoundaryInclusion d) a c (TopCat.ofHom (g.level l))) :
        ∃ (a : cubeBoundaryObject d ⟶ (X.level l).space)
          (c : cubeObject d ⟶ (Y.level l).space),
          IsPushout (cubeBoundaryInclusion d) a c
            (TopCat.ofHom ((eqToHom hX ≫ g ≫ eqToHom hY).level l)) := by
      subst X'
      subst Y'
      exact hh
    apply transport
    rw [show r+1+k = (r+k)+1 by omega]
    exact ih

/-- Below the generating level the original free map is an isomorphism;
these padded levels add no topological cells. -/
theorem freeMap_level_isIso_below (r : ℕ) {A B : BasedSpace.{u}}
    (f : A ⟶ B) (k : ℕ) (hk : k < r) :
    IsIso (TopCat.ofHom ((freeMap r f).level k)) := by
  induction r generalizing k with
  | zero => omega
  | succ r ih =>
    rw [freeMap_succ]
    have transport {X X' Y Y' : Prespectrum.{u}} (hX : X = X') (hY : Y' = Y)
        (g : X' ⟶ Y') (l : ℕ)
        (hh : IsIso (TopCat.ofHom (g.level l))) :
        IsIso (TopCat.ofHom ((eqToHom hX ≫ g ≫ eqToHom hY).level l)) := by
      subst X'
      subst Y'
      exact hh
    apply transport
    cases k with
    | zero => exact inferInstanceAs (IsIso (𝟙 (TopCat.of PUnit)))
    | succ k => exact ih k (by omega)

end KIP126.AdamsSynthetic.Source.Prespectrum
