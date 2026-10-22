module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyGroup/Map/Stability/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Map.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

theorem Hom.levelHomotopy_stabilize {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n r : ℕ) (x : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    f.levelHomotopy (n+1) (r+1) (stabilizeHomotopy X n r x) =
      stabilizeHomotopy Y n r (f.levelHomotopy n r x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro t
    exact f.bond n _ _

theorem Hom.stableLevelTransition_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) (i k : ℕ) (h : i ≤ k) (x : stableLevelGroup X d i) :
    f.levelHomotopy (stableGroupStage d k) (stableGroupDimension d k)
        (stableLevelTransition X d i k h x) =
      stableLevelTransition Y d i k h
        (f.levelHomotopy (stableGroupStage d i) (stableGroupDimension d i) x) := by
  induction h with
  | refl => rw [stableLevelTransition_self, stableLevelTransition_self]; rfl
  | @step k h ih =>
    rw [stableLevelTransition_succ X d h, stableLevelTransition_succ Y d h]
    exact (f.levelHomotopy_stabilize _ _ _).trans
      (congrArg (stabilizeHomotopy Y (stableGroupStage d k) (stableGroupDimension d k)) ih)

/-- Levelwise injectivity of the actual homotopy maps implies injectivity
on the originally defined stable quotient. -/
theorem stableHomotopyMap_injective_of_levelHomotopy_injective
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n r, Function.Injective (f.levelHomotopy n r)) (d : ℤ) :
    Function.Injective (stableHomotopyMap f d) := by
  intro x y h
  obtain ⟨k,p,q,rfl,rfl⟩ := exists_stableLevelClass_pair X d x y
  have hc := congrArg (stableGroupCode Y d) h
  simp only [stableLevelClass_natural, stableGroupCode_levelClass] at hc
  obtain ⟨j,hp,hq,hpq⟩ := Quotient.exact hc
  apply (stableHomotopyGroupEquiv X d).injective
  change stableGroupCode X d (stableLevelClass X d k p) =
    stableGroupCode X d (stableLevelClass X d k q)
  rw [stableGroupCode_levelClass, stableGroupCode_levelClass]
  apply Quotient.sound
  refine ⟨j,hp,hq,hf _ _ ?_⟩
  rw [f.stableLevelTransition_natural, f.stableLevelTransition_natural]
  exact hpq

/-- A levelwise surjection on actual homotopy classes gives a surjection
on actual stable classes, using a representative at one cofinal stage. -/
theorem stableHomotopyMap_surjective_of_levelHomotopy_surjective
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n r, Function.Surjective (f.levelHomotopy n r)) (d : ℤ) :
    Function.Surjective (stableHomotopyMap f d) := by
  intro y
  obtain ⟨k,p,_,hy,_⟩ := exists_stableLevelClass_pair Y d y y
  obtain ⟨q,hq⟩ := hf (stableGroupStage d k) (stableGroupDimension d k) p
  refine ⟨stableLevelClass X d k q, ?_⟩
  rw [stableLevelClass_natural, hq]
  exact hy.symm

/-- An actual prespectrum map inducing levelwise homotopy bijections is
a stable equivalence in the original point-set definition. -/
theorem stableEquivalence_of_levelHomotopy_bijective
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n r, Function.Bijective (f.levelHomotopy n r)) :
    stableEquivalences f :=
  fun d => ⟨stableHomotopyMap_injective_of_levelHomotopy_injective f (fun n r => (hf n r).1) d,
    stableHomotopyMap_surjective_of_levelHomotopy_surjective f (fun n r => (hf n r).2) d⟩

end KIP126.AdamsSynthetic.Source.Prespectrum
