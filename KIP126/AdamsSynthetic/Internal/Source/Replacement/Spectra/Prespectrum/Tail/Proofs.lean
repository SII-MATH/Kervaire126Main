module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Tail/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Tail.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyFunctor.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem desuspensionStableHomotopyLift_bijective (X : Prespectrum.{u}) (d : ℤ) :
    Function.Bijective (desuspensionStableHomotopyLift X d) := by
  let R (a : Representative (desuspension X) d) : Representative X (d+1) :=
    ⟨a.stage,a.dimension+1,by have := a.degree; omega,
      stabilizeLoop (desuspension X) a.stage a.dimension a.loop⟩
  have respects (a b : Representative (desuspension X) d)
      (hab : StableRelation (desuspension X) d a b) :
      Quot.mk (StableRelation X (d+1)) (R a) = Quot.mk _ (R b) := by
    cases hab with
    | homotopy p hp => exact Quot.sound (StableRelation.homotopy (R a) _
        (stabilizeLoop_homotopic (desuspension X) _ _ _ _ hp))
    | stabilization => exact Quot.sound (StableRelation.stabilization (R a))
  let G : StableHomotopy (desuspension X) d → StableHomotopy X (d+1) :=
    Quot.lift (fun a => Quot.mk _ (R a)) respects
  have hl : Function.LeftInverse G (desuspensionStableHomotopyLift X d) := by
    intro a
    induction a using Quot.inductionOn with
    | h a =>
      change Quot.mk _ (R a.pad) = Quot.mk _ a
      exact (Quot.sound (StableRelation.stabilization a)).symm
  have hr : Function.RightInverse G (desuspensionStableHomotopyLift X d) := by
    intro a
    induction a using Quot.inductionOn with
    | h a =>
      change Quot.mk _ (R a).pad = Quot.mk _ a
      exact (Quot.sound (StableRelation.stabilization a)).symm
  exact ⟨hl.injective,hr.surjective⟩

theorem desuspensionStableHomotopyLift_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) (x : StableHomotopy X (d+1)) :
    stableHomotopyMap (desuspensionMap f) d (desuspensionStableHomotopyLift X d x) =
      desuspensionStableHomotopyLift Y d (stableHomotopyMap f (d+1) x) := by
  induction x using Quot.inductionOn with | h a => rfl

theorem desuspensionMap_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (desuspensionMap f) := by
  intro d
  have hx := desuspensionStableHomotopyLift_bijective X d
  have hy := desuspensionStableHomotopyLift_bijective Y d
  constructor
  · intro a b hab
    obtain ⟨a,rfl⟩ := hx.2 a
    obtain ⟨b,rfl⟩ := hx.2 b
    rw [desuspensionStableHomotopyLift_natural,desuspensionStableHomotopyLift_natural] at hab
    exact congrArg _ ((hf (d+1)).1 (hy.1 hab))
  · intro b
    obtain ⟨b,rfl⟩ := hy.2 b
    obtain ⟨a,rfl⟩ := (hf (d+1)).2 b
    exact ⟨desuspensionStableHomotopyLift X d a,desuspensionStableHomotopyLift_natural f d a⟩

theorem suspensionSpectrum_tail (A : BasedSpace.{u}) :
    suspensionSpectrum A.suspension = levelTail (suspensionSpectrum A) := by
  have h (n : ℕ) : A.suspension.iterateSuspension n = A.iterateSuspension (n+1) := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg BasedSpace.suspension ih
  have ext (X Y : Prespectrum.{u}) (hlevel : X.level = Y.level)
      (hbond : ∀ n, HEq (X.bond n) (Y.bond n)) : X = Y := by
    cases X
    cases Y
    cases hlevel
    have hb := funext fun n => eq_of_heq (hbond n)
    cases hb
    rfl
  apply ext _ _ (funext h)
  intro n
  have hp (A B : BasedSpace.{u}) (hab : A = B) :
      HEq A.suspensionProjection B.suspensionProjection := by cases hab; rfl
  exact hp _ _ (h n)

theorem free_succ (n : ℕ) (A : BasedSpace.{u}) :
    free (n+1) A = desuspension (free n A) :=
  Function.iterate_succ_apply' desuspension n (suspensionSpectrum A)

@[simp] theorem evaluationFunctor_desuspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) : (evaluationFunctor (n+1)).map (desuspensionMap f) =
      (evaluationFunctor n).map f := rfl

@[simp] theorem levelTail_desuspension (X : Prespectrum.{u}) : levelTail (desuspension X) = X := rfl

@[simp] theorem levelTailMap_desuspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    levelTailMap (desuspensionMap f) = f := rfl

theorem paddedTailInclusion_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    desuspensionMap (levelTailMap f) ≫ paddedTailInclusion Y = paddedTailInclusion X ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero => exact (f.point 0).symm
  | succ n => rfl

theorem desuspensionMap_stableEquivalence_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (desuspensionMap f) ↔ stableEquivalences f := by
  refine ⟨?_,desuspensionMap_stableEquivalence f⟩
  intro hf d
  have h (e : ℤ) : Function.Bijective (stableHomotopyMap f (e+1)) := by
    have hx := desuspensionStableHomotopyLift_bijective X e
    have hy := desuspensionStableHomotopyLift_bijective Y e
    constructor
    · intro a b hab
      apply hx.1
      apply (hf e).1
      rw [desuspensionStableHomotopyLift_natural,desuspensionStableHomotopyLift_natural,hab]
    · intro b
      obtain ⟨a,ha⟩ := (hf e).2 (desuspensionStableHomotopyLift Y e b)
      obtain ⟨a,rfl⟩ := hx.2 a
      refine ⟨a,hy.1 ?_⟩
      rw [← desuspensionStableHomotopyLift_natural]
      exact ha
  convert h (d-1) using 1 <;> congr 1 <;> omega

theorem levelTailMap_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (levelTailMap f) := by
  apply (desuspensionMap_stableEquivalence_iff _).mp
  apply (stableEquivalence_iff_source_isIso _).mpr
  haveI : IsIso (sourceLocalization.map (paddedTailInclusion X)) := paddedTailInclusion_isIso X
  haveI : IsIso (sourceLocalization.map (paddedTailInclusion Y)) := paddedTailInclusion_isIso Y
  haveI : IsIso (sourceLocalization.map f) := stableEquivalences.Q_inverts _ hf
  have h := congrArg sourceLocalization.map (paddedTailInclusion_natural f)
  rw [Functor.map_comp,Functor.map_comp] at h
  have he : sourceLocalization.map (desuspensionMap (levelTailMap f)) =
      sourceLocalization.map (paddedTailInclusion X) ≫ sourceLocalization.map f ≫
        inv (sourceLocalization.map (paddedTailInclusion Y)) := by
    apply (cancel_mono (sourceLocalization.map (paddedTailInclusion Y))).mp
    simpa only [Category.assoc,IsIso.inv_hom_id,Category.comp_id] using h
  rw [he]
  infer_instance

end KIP126.AdamsSynthetic.Source.Prespectrum
