module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/Lifting/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory
open KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Right lifting against the actual free cubical generators fills every
full cube-boundary lifting problem at every original spectrum level. -/
theorem hasCubeBoundaryLifting_of_cubicalCellBoundary
    {X Y : Prespectrum.{u}} (q : X ⟶ Y)
    (hq : ∀ i, HasLiftingProperty (cubicalCellBoundary i) q) (n : ℕ) :
    HasCubeBoundaryLifting (q.level n) := by
  intro r g H hcomm
  letI : HasLiftingProperty (BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{u} r))
      ((evaluationFunctor n).map q) :=
    (freeMap_hasLiftingProperty_iff n _ q).mp (hq (n,r))
  let g₀ : C(cubeBoundaryObject.{u} r,X.level n) :=
    g.comp ⟨ULift.down,continuous_uliftDown⟩
  let H₀ : C(cubeObject.{u} r,Y.level n) :=
    H.comp ⟨ULift.down,continuous_uliftDown⟩
  let g' := (BasedSpace.adjoinPointEquiv (cubeBoundaryObject.{u} r) (X.level n)).symm g₀
  let H' := (BasedSpace.adjoinPointEquiv (cubeObject.{u} r) (Y.level n)).symm H₀
  have sq : CommSq g' (BasedSpace.adjoinPointMap (cubeBoundaryInclusion r))
      ((evaluationFunctor n).map q) H' := by
    constructor
    apply (BasedSpace.adjoinPointEquiv (cubeBoundaryObject.{u} r) (Y.level n)).injective
    rw [BasedSpace.adjoinPointEquiv_precomp,BasedSpace.adjoinPointEquiv_postcomp]
    dsimp only [g',H']
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro x
    exact hcomm x.down
  let L : C(Fin r → I,X.level n) := sq.lift.map.comp
    ⟨fun x => Sum.inl (ULift.up x),continuous_inl.comp continuous_uliftUp⟩
  refine ⟨L,?_,?_⟩
  · intro x
    exact congrArg (fun f => f.map (Sum.inl (ULift.up x))) sq.fac_right
  · intro x
    exact congrArg (fun f => f.map (Sum.inl (ULift.up x))) sq.fac_left

/-- The actual free-cell lifting property proves a stable equivalence
using genuine level homotopy bijections, in all nonnegative dimensions. -/
theorem stableEquivalence_of_cubicalCellBoundary_lifting
    {X Y : Prespectrum.{u}} (q : X ⟶ Y)
    (hq : ∀ i, HasLiftingProperty (cubicalCellBoundary i) q) : stableEquivalences q := by
  apply stableEquivalence_of_levelHomotopy_bijective q
  intro n r
  exact (hasCubeBoundaryLifting_of_cubicalCellBoundary q hq n).continuousHomotopyMap_bijective
    (X.level n).point (Y.level n).point (q.point n) r

end KIP126.AdamsSynthetic.Source.Prespectrum
