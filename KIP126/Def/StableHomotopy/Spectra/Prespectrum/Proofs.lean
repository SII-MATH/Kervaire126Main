module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-! Cofinal representatives and vanishing for the actual point-set stable
homotopy quotient. These arguments use only its displayed stabilization and
based-homotopy relations; no completion or spectrum-model input is used. -/

namespace KIP126.StableHomotopy.Spectra.Prespectrum

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

/-- Any finite number of actual bonding maps preserves the stable class. -/
theorem Representative.class_eq_iterate_next (a : Representative X d) (k : ℕ) :
    (Quot.mk (StableRelation X d) a : StableHomotopy X d) =
      Quot.mk _ ((Representative.next^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Quot.sound (StableRelation.stabilization _))

/-- Based homotopies give equality of the displayed stable classes. -/
theorem loopClass_eq_of_homotopic (n r : ℕ) (hr : (r : ℤ) = d + n)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point)
    (h : GenLoop.Homotopic p q) : loopClass X d n r hr p = loopClass X d n r hr q :=
  Quot.sound (StableRelation.homotopy ⟨n, r, hr, p⟩ q h)

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

end KIP126.StableHomotopy.Spectra.Prespectrum
