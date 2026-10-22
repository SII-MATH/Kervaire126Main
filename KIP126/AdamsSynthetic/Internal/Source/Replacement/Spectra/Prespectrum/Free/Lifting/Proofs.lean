module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Free/Lifting/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Tail.Data
import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual free/evaluation equivalence transfers the precise right
lifting property, retaining the existing free map and level map. -/
theorem freeMap_hasLiftingProperty_iff (n : ℕ)
    {A B : BasedSpace.{u}} (i : A ⟶ B) {X Y : Prespectrum.{u}} (q : X ⟶ Y) :
    HasLiftingProperty (freeMap n i) q ↔
      HasLiftingProperty i ((evaluationFunctor n).map q) := by
  constructor
  · intro h
    letI := h
    constructor
    intro t b sq
    let t' := (freeEvaluation n A X).symm t
    let b' := (freeEvaluation n B Y).symm b
    have sq' : CommSq t' (freeMap n i) q b' := by
      constructor
      apply (freeEvaluation n A Y).injective
      rw [freeEvaluation_freeMap_comp,freeEvaluation_natural]
      dsimp only [t',b']
      rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
      exact sq.w
    refine CommSq.HasLift.mk' {
      l := freeEvaluation n B X sq'.lift
      fac_left := ?_
      fac_right := ?_ }
    · have h := congrArg (freeEvaluation n A X) sq'.fac_left
      rw [freeEvaluation_freeMap_comp] at h
      exact h.trans (Equiv.apply_symm_apply _ t)
    · have h := congrArg (freeEvaluation n B Y) sq'.fac_right
      rw [freeEvaluation_natural] at h
      exact h.trans (Equiv.apply_symm_apply _ b)
  · intro h
    letI := h
    constructor
    intro t b sq
    have sq' : CommSq (freeEvaluation n A X t) i ((evaluationFunctor n).map q)
        (freeEvaluation n B Y b) := by
      constructor
      have h := congrArg (freeEvaluation n A Y) sq.w
      rw [freeEvaluation_freeMap_comp,freeEvaluation_natural] at h
      exact h
    refine CommSq.HasLift.mk' {
      l := (freeEvaluation n B X).symm sq'.lift
      fac_left := ?_
      fac_right := ?_ }
    · apply (freeEvaluation n A X).injective
      rw [freeEvaluation_freeMap_comp,Equiv.apply_symm_apply]
      exact sq'.fac_left
    · apply (freeEvaluation n B Y).injective
      rw [freeEvaluation_natural,Equiv.apply_symm_apply]
      exact sq'.fac_right

end KIP126.AdamsSynthetic.Source.Prespectrum
