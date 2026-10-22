module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum
import Mathlib.Logic.Function.Iterate

@[expose] section

/-! Cofinal representatives and vanishing for the actual point-set stable
homotopy quotient. These arguments use only its displayed stabilization and
based-homotopy relations; no completion or spectrum-model input is used. -/

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open Topology
open scoped Topology.Homotopy unitInterval

universe u

variable {X : Prespectrum.{u}} {d : ℤ}

/-- The bonding map sends a constant cubical loop to a constant loop. -/
@[simp] theorem stabilizeLoop_const (n r : ℕ) :
    stabilizeLoop X n r GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact X.bond_point n (t 0)

@[simp] theorem Representative.iterate_next_stage (a : Representative X d) (k : ℕ) :
    ((Representative.next^[k]) a).stage = a.stage + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((Representative.next^[k]) a).stage + 1 = _
    omega

@[simp] theorem Representative.iterate_next_dimension (a : Representative X d) (k : ℕ) :
    ((Representative.next^[k]) a).dimension = a.dimension + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((Representative.next^[k]) a).dimension + 1 = _
    omega

/-- Any finite number of actual bonding maps preserves the stable class. -/
theorem Representative.class_eq_iterate_next (a : Representative X d) (k : ℕ) :
    (Quot.mk (StableRelation X d) a : StableHomotopy X d) =
      Quot.mk _ ((Representative.next^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Quot.sound (StableRelation.stabilization _))

theorem Representative.iterate_next_loop_const (a : Representative X d)
    (h : a.loop = GenLoop.const) (k : ℕ) :
    ((Representative.next^[k]) a).loop = GenLoop.const := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change stabilizeLoop X _ _ _ = _
    rw [ih, stabilizeLoop_const]
    rfl

/-- Based homotopies give equality of the displayed stable classes. -/
theorem loopClass_eq_of_homotopic (n r : ℕ) (hr : (r : ℤ) = d + n)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point)
    (h : GenLoop.Homotopic p q) : loopClass X d n r hr p = loopClass X d n r hr q :=
  Quot.sound (StableRelation.homotopy ⟨n, r, hr, p⟩ q h)

/-- A stable class has a representative above any prescribed stage. -/
theorem exists_representative_stage_ge (x : StableHomotopy X d) (N : ℕ) :
    ∃ a : Representative X d, N ≤ a.stage ∧ Quot.mk (StableRelation X d) a = x := by
  induction x using Quot.inductionOn with
  | h a =>
    refine ⟨(Representative.next^[N]) a, ?_, ?_⟩
    · simp only [Representative.iterate_next_stage]
      omega
    · exact (a.class_eq_iterate_next N).symm

/-- Representatives at the same stage have the same stable class whenever
the corresponding ordinary based homotopy set is trivial. -/
theorem Representative.class_eq_of_stage_eq (a b : Representative X d)
    (hab : a.stage = b.stage)
    (h : Subsingleton (_root_.HomotopyGroup (Fin a.dimension)
      (X.level a.stage) (X.level a.stage).point)) :
    (Quot.mk (StableRelation X d) a : StableHomotopy X d) = Quot.mk _ b := by
  rcases a with ⟨n, r, hr, p⟩
  rcases b with ⟨m, s, hs, q⟩
  dsimp only at hab h
  subst m
  have hrs : r = s := by omega
  subst s
  have hpq : GenLoop.Homotopic p q :=
    Quotient.exact (h.elim
      (⟦p⟧ : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) ⟦q⟧)
  exact Quot.sound (StableRelation.homotopy ⟨n, r, hr, p⟩ q hpq)

/-- Eventual vanishing of the level homotopy sets in degree `d + n`
implies vanishing in stable degree `d`. The two representatives are moved
to one common stage before applying the levelwise hypothesis. -/
theorem stableHomotopy_subsingleton_of_eventually_level_homotopy_subsingleton
    (N : ℕ)
    (h : ∀ (n : ℕ), N ≤ n → ∀ (r : ℕ), (r : ℤ) = d + n →
      Subsingleton (_root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point)) :
    Subsingleton (StableHomotopy X d) := by
  constructor
  intro x y
  induction x using Quot.inductionOn with
  | h a =>
    induction y using Quot.inductionOn with
    | h b =>
      let K := max N (max a.stage b.stage)
      let a' := (Representative.next^[K - a.stage]) a
      let b' := (Representative.next^[K - b.stage]) b
      have ha : a'.stage = K := by
        dsimp only [a']
        rw [Representative.iterate_next_stage]
        omega
      have hb : b'.stage = K := by
        dsimp only [b']
        rw [Representative.iterate_next_stage]
        omega
      calc
        Quot.mk _ a = Quot.mk _ a' := a.class_eq_iterate_next _
        _ = Quot.mk _ b' := a'.class_eq_of_stage_eq b' (ha.trans hb.symm)
          (h a'.stage (by rw [ha]; exact le_max_left _ _) a'.dimension a'.degree)
        _ = Quot.mk _ b := (b.class_eq_iterate_next _).symm

/-- The vanishing criterion in terms of actual nullhomotopies of cubical
representatives, before taking any ordinary or stable homotopy quotient. -/
theorem stableHomotopy_subsingleton_of_eventually_nullhomotopic
    (N : ℕ)
    (h : ∀ (n : ℕ), N ≤ n → ∀ (r : ℕ), (r : ℤ) = d + n →
      ∀ p : GenLoop (Fin r) (X.level n) (X.level n).point,
        GenLoop.Homotopic p GenLoop.const) :
    Subsingleton (StableHomotopy X d) := by
  apply stableHomotopy_subsingleton_of_eventually_level_homotopy_subsingleton N
  intro n hn r hr
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q => exact Quotient.sound ((h n hn r hr p).trans (h n hn r hr q).symm)

/-- Stabilization sends an actual based cubical homotopy to a based homotopy. -/
theorem stabilizeLoop_homotopic (P : Prespectrum.{u}) (n r : ℕ)
    (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
  obtain ⟨H⟩ := h
  refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
            continuous_toFun := (P.bond n).continuous.comp
              ((H.continuous.comp (continuous_fst.prodMk
                (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                  ((continuous_apply 0).comp continuous_snd))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    change P.bond n (H (0,_),_) = _
    rw [H.apply_zero]
    rfl
  · intro t
    change P.bond n (H (1,_),_) = _
    rw [H.apply_one]
    rfl
  · intro s t ht
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with h | h
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_zero,P.bond_zero]
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_one,P.bond_one]
    | succ j =>
      change P.bond n (H (s,_),_) = P.bond n (p _,_)
      rw [H.eq_fst s ⟨j,hi⟩]
      rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
