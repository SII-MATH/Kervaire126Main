module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyGroup/Abelian/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Abelian.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open Topology
open scoped Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

/-- Addition is exactly concatenation of actual cofinal loop representatives. -/
theorem stableLevelClass_mul (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (x y : stableLevelGroup X d k) :
    stableLevelClass X d k (x * y) = stableLevelClass X d k x + stableLevelClass X d k y := by
  apply (stableHomotopyAddEquiv X d).injective
  rw [map_add]
  change Additive.ofMul (stableGroupCode X d (stableLevelClass X d k (x * y))) =
    Additive.ofMul (stableGroupCode X d (stableLevelClass X d k x)) +
      Additive.ofMul (stableGroupCode X d (stableLevelClass X d k y))
  rw [stableGroupCode_levelClass, stableGroupCode_levelClass, stableGroupCode_levelClass]
  exact congrArg Additive.ofMul (DirectLimit.mul_def k x y).symm

theorem stableLevelClass_one (X : Prespectrum.{u}) (d : ℤ) (k : ℕ) :
    stableLevelClass X d k 1 = 0 := by
  apply (stableHomotopyAddEquiv X d).injective
  rw [map_zero]
  change Additive.ofMul (stableGroupCode X d (stableLevelClass X d k 1)) = 0
  rw [stableGroupCode_levelClass]
  exact congrArg Additive.ofMul (DirectLimit.one_def k).symm

/-- The constant loop at any allowable stage is the constructed group zero. -/
theorem loopClass_const (X : Prespectrum.{u}) (d : ℤ) (n r : ℕ)
    (hr : (r : ℤ) = d + n) : loopClass X d n r hr GenLoop.const = 0 := by
  apply (stableHomotopyAddEquiv X d).injective
  rw [map_zero]
  let a : Representative X d := ⟨n,r,hr,GenLoop.const⟩
  change Additive.ofMul a.groupColimit = 0
  unfold Representative.groupColimit
  rw [Representative.atStableLevel_const _ _ _ (a.iterate_next_loop_const rfl _)]
  exact congrArg Additive.ofMul (DirectLimit.one_def a.stage).symm

theorem stableLevelClass_transAt (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (i : Fin (stableGroupDimension d k))
    (p q : GenLoop (Fin (stableGroupDimension d k))
      (X.level (stableGroupStage d k)) (X.level (stableGroupStage d k)).point) :
    stableLevelClass X d k ⟦GenLoop.transAt i p q⟧ =
      stableLevelClass X d k ⟦p⟧ + stableLevelClass X d k ⟦q⟧ := by
  let x : stableLevelGroup X d k := ⟦q⟧
  let y : stableLevelGroup X d k := ⟦p⟧
  have hm : x * y = ⟦GenLoop.transAt i p q⟧ :=
    _root_.HomotopyGroup.mul_spec (i := i) (p := q) (q := p)
  exact (congrArg (stableLevelClass X d k) hm).symm.trans
    ((stableLevelClass_mul X d k x y).trans (add_comm _ _))

private theorem loopClass_transAt_of_stage_ge (X : Prespectrum.{u}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d + n) (hn : stableGroupStage d 0 ≤ n)
    (i : Fin r) (p q : GenLoop (Fin r) (X.level n) (X.level n).point) :
    loopClass X d n r h (GenLoop.transAt i p q) =
      loopClass X d n r h p + loopClass X d n r h q := by
  obtain ⟨k,hnk⟩ : ∃ k, n = stableGroupStage d k :=
    ⟨n - stableGroupStage d 0, by unfold stableGroupStage at *; omega⟩
  subst n
  have hr : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  exact stableLevelClass_transAt X d k i p q

private theorem loopClass_transAt_after (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (n r : ℕ) (h : (r : ℤ) = d + n) (hn : stableGroupStage d 0 ≤ n + k)
    (i : Fin r) (p q : GenLoop (Fin r) (X.level n) (X.level n).point) :
    loopClass X d n r h (GenLoop.transAt i p q) =
      loopClass X d n r h p + loopClass X d n r h q := by
  induction k generalizing n r with
  | zero => exact loopClass_transAt_of_stage_ge X d n r h hn i p q
  | succ k ih =>
    have hs : ((r + 1 : ℕ) : ℤ) = d + (n + 1 : ℕ) := by omega
    have hc (a : GenLoop (Fin r) (X.level n) (X.level n).point) :
        loopClass X d n r h a = loopClass X d (n + 1) (r + 1) hs (stabilizeLoop X n r a) :=
      Quot.sound (StableRelation.stabilization _)
    calc
      _ = loopClass X d (n + 1) (r + 1) hs (stabilizeLoop X n r (GenLoop.transAt i p q)) := hc _
      _ = loopClass X d (n + 1) (r + 1) hs
          (GenLoop.transAt i.succ (stabilizeLoop X n r p) (stabilizeLoop X n r q)) :=
        congrArg (loopClass X d (n + 1) (r + 1) hs) (stabilizeLoop_transAt X n r i p q)
      _ = loopClass X d (n + 1) (r + 1) hs (stabilizeLoop X n r p) +
          loopClass X d (n + 1) (r + 1) hs (stabilizeLoop X n r q) :=
        ih (n + 1) (r + 1) hs (by omega) i.succ _ _
      _ = _ := congrArg₂ (· + ·) (hc p).symm (hc q).symm

/-- At every stage and in every available coordinate, actual loop
concatenation gives the constructed stable addition. -/
theorem loopClass_transAt (X : Prespectrum.{u}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d + n) (i : Fin r)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point) :
    loopClass X d n r h (GenLoop.transAt i p q) =
      loopClass X d n r h p + loopClass X d n r h q :=
  loopClass_transAt_after X d (stableGroupStage d 0) n r h (by omega) i p q

end KIP126.AdamsSynthetic.Source.Prespectrum
