module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyGroup/Colimit/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Colimit.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open Topology
open scoped Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

theorem Representative.atStableLevel_congr {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative X d} (hab : a = b) (k : ℕ)
    (ha : a.stage = stableGroupStage d k) (hb : b.stage = stableGroupStage d k) :
    a.atStableLevel k ha = b.atStableLevel k hb := by
  subst b
  rfl

theorem Representative.atStableLevel_sigma_congr {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) {k l : ℕ} (hkl : k = l)
    (hk : a.stage = stableGroupStage d k) (hl : a.stage = stableGroupStage d l) :
    (⟨k,a.atStableLevel k hk⟩ : Σ j, stableLevelGroup X d j) = ⟨l,a.atStableLevel l hl⟩ := by
  subst l
  rfl

theorem Representative.atStableLevel_next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k) :
    a.next.atStableLevel (k + 1) (by change a.stage + 1 = _; rw [h]; rfl) =
      stableLevelBond X d k (a.atStableLevel k h) := by
  rcases a with ⟨n,r,hr,p⟩
  dsimp only at h
  subst n
  have hd : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  rfl

theorem Representative.atStableLevel_homotopy {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (hs : a.stage = stableGroupStage d k)
    (p : GenLoop (Fin a.dimension) (X.level a.stage) (X.level a.stage).point)
    (h : GenLoop.Homotopic a.loop p) :
    a.atStableLevel k hs = ({a with loop := p} : Representative X d).atStableLevel k hs := by
  rcases a with ⟨n,r,hr,q⟩
  dsimp only at hs h p
  subst n
  have hd : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  exact Quotient.sound h

theorem Representative.iterate_next_homotopy {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d)
    (p : GenLoop (Fin a.dimension) (X.level a.stage) (X.level a.stage).point)
    (h : GenLoop.Homotopic a.loop p) (k : ℕ) :
    ∃ q, (Representative.next^[k]) {a with loop := p} =
        { (Representative.next^[k]) a with loop := q } ∧
      GenLoop.Homotopic ((Representative.next^[k]) a).loop q := by
  induction k with
  | zero => exact ⟨p,rfl,h⟩
  | succ k ih =>
    obtain ⟨q,hq,hh⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hq]
    exact ⟨stabilizeLoop X _ _ q, rfl, stabilizeLoop_homotopic X _ _ _ _ hh⟩

theorem Representative.groupColimit_homotopy {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d)
    (p : GenLoop (Fin a.dimension) (X.level a.stage) (X.level a.stage).point)
    (h : GenLoop.Homotopic a.loop p) :
    a.groupColimit = ({a with loop := p} : Representative X d).groupColimit := by
  obtain ⟨q,hq,hh⟩ := a.iterate_next_homotopy p h (stableGroupStage d 0)
  unfold Representative.groupColimit
  dsimp only
  congr 2
  simpa only [hq] using Representative.atStableLevel_homotopy
    ((Representative.next^[stableGroupStage d 0]) a) a.stage
    (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega) q hh

theorem Representative.groupColimit_next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) : a.groupColimit = a.next.groupColimit := by
  unfold Representative.groupColimit
  have heq : (Representative.next^[stableGroupStage d 0]) a.next =
      ((Representative.next^[stableGroupStage d 0]) a).next :=
    (Function.iterate_succ_apply _ _ _).symm.trans (Function.iterate_succ_apply' _ _ _)
  change (⟦⟨a.stage,_⟩⟧ : stableGroupColimit X d) = ⟦⟨a.stage + 1,_⟩⟧
  have hnext := Representative.atStableLevel_next
    ((Representative.next^[stableGroupStage d 0]) a) a.stage
    (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega)
  have hlevel := DirectLimit.eq_of_le
    (f := stableLevelTransition X d)
    ⟨a.stage, ((Representative.next^[stableGroupStage d 0]) a).atStableLevel a.stage
      (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega)⟩
    (a.stage + 1) (Nat.le_succ _)
  rw [stableLevelTransition_succ X d (Nat.le_refl _), stableLevelTransition_self] at hlevel
  refine hlevel.trans (congrArg (Quotient.mk (DirectLimit.setoid (stableLevelTransition X d)))
    (congrArg (Sigma.mk (a.stage + 1)) ?_))
  exact hnext.symm.trans (Representative.atStableLevel_congr heq.symm _ _ _)

theorem stableLevelClass_bond (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (x : stableLevelGroup X d k) :
    stableLevelClass X d k x = stableLevelClass X d (k + 1) (stableLevelBond X d k x) := by
  induction x using Quotient.inductionOn with
  | h p => exact Quot.sound (StableRelation.stabilization _)

theorem stableLevelClass_transition (X : Prespectrum.{u}) (d : ℤ)
    (i j : ℕ) (h : i ≤ j) (x : stableLevelGroup X d i) :
    stableLevelClass X d i x = stableLevelClass X d j (stableLevelTransition X d i j h x) := by
  induction h with
  | refl => rw [stableLevelTransition_self]; rfl
  | @step j h ih =>
    rw [stableLevelTransition_succ X d h]
    exact ih.trans (stableLevelClass_bond X d j _)

theorem Representative.atStableLevel_iterate {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k) (j : ℕ) :
    ((Representative.next^[j]) a).atStableLevel (k + j)
        (by rw [Representative.iterate_next_stage, h]; unfold stableGroupStage; omega) =
      stableLevelTransition X d k (k + j) (Nat.le_add_right _ _) (a.atStableLevel k h) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero, stableLevelTransition_self,
      MonoidHom.id_apply]
  | succ j ih =>
    refine (Representative.atStableLevel_congr (Function.iterate_succ_apply' _ _ _) _ _
      (by change ((Representative.next^[j]) a).stage + 1 = _
          rw [Representative.iterate_next_stage, h]
          unfold stableGroupStage
          omega)).trans ?_
    exact (Representative.atStableLevel_next ((Representative.next^[j]) a) (k + j)
        (by rw [Representative.iterate_next_stage, h]; unfold stableGroupStage; omega)).trans
      ((congrArg (stableLevelBond X d (k + j)) ih).trans
        (DFunLike.congr_fun (stableLevelTransition_succ X d (Nat.le_add_right k j))
          (a.atStableLevel k h)).symm)

theorem Representative.groupColimit_atStableLevel {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k) :
    a.groupColimit = (⟦⟨k,a.atStableLevel k h⟩⟧ : stableGroupColimit X d) := by
  have hs : k + stableGroupStage d 0 = a.stage := by rw [h]; unfold stableGroupStage; omega
  have hi := a.atStableLevel_iterate k h (stableGroupStage d 0)
  have he := DirectLimit.eq_of_le (f := stableLevelTransition X d)
    ⟨k, a.atStableLevel k h⟩ (k + stableGroupStage d 0) (Nat.le_add_right _ _)
  unfold Representative.groupColimit
  rw [← hi] at he
  exact (congrArg (Quotient.mk (DirectLimit.setoid (stableLevelTransition X d)))
    (Representative.atStableLevel_sigma_congr _ hs _ _)).symm.trans
    he.symm

theorem stableLevelClass_atStableLevel {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k) :
    stableLevelClass X d k (a.atStableLevel k h) = Quot.mk _ a := by
  rcases a with ⟨n,r,hr,p⟩
  dsimp only at h
  subst n
  have hd : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  rfl

theorem Representative.atStableLevel_const {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k)
    (hl : a.loop = GenLoop.const) : a.atStableLevel k h = 1 := by
  rcases a with ⟨n,r,hr,p⟩
  dsimp only at h hl
  subst n
  have hd : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  exact congrArg Quotient.mk' hl

end KIP126.AdamsSynthetic.Source.Prespectrum
