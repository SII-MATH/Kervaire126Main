module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import Mathlib.Order.KonigLemma
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.Abel

/-! Finite-kernel inverse-tower arguments used by the archived sphere BHS
proof. Every assertion is proved with its actual algebraic hypotheses.
These private lemmas assert no completeness of the selected ordinary sphere.
-/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
universe u v w

/-- Nonempty finite terms with arbitrary adjacent restriction maps admit a
compatible dependent inverse sequence. The point at the initial index is
not prescribed, and the restriction maps need not be surjective. -/
private theorem exists_compatible_of_finite (m₀ : ℕ)
    (A : (m : ℕ) → m₀ ≤ m → Type u)
    (restrict : ∀ (m : ℕ) (hm : m₀ ≤ m),
      A (m + 1) (Nat.le_succ_of_le hm) → A m hm)
    (hfinite : ∀ (m : ℕ) (hm : m₀ ≤ m), Finite (A m hm))
    (hne : ∀ (m : ℕ) (hm : m₀ ≤ m), Nonempty (A m hm)) :
    ∃ a : ∀ (m : ℕ) (hm : m₀ ≤ m), A m hm,
      ∀ (m : ℕ) (hm : m₀ ≤ m),
        restrict m hm (a (m + 1) (Nat.le_succ_of_le hm)) = a m hm := by
  classical
  let B (m : ℕ) := ∀ hm : m₀ ≤ m, A m hm
  let step (m : ℕ) (b : B (m + 1)) : B m :=
    fun hm => restrict m hm (b (Nat.le_succ_of_le hm))
  letI : ∀ m, Finite (B m) := fun m => by
    letI : ∀ hm : m₀ ≤ m, Finite (A m hm) := hfinite m
    exact Pi.finite
  letI : ∀ m, Nonempty (B m) :=
    fun m => ⟨fun hm => Classical.choice (hne m hm)⟩
  let π : {i j : ℕ} → i ≤ j → B j → B i :=
    fun {_ _} hij b => Nat.decreasingInduction (fun k _ => step k) b hij
  obtain ⟨a, ha⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun {_} _ => Nat.decreasingInduction_self _ _)
    (by
      intro i j k hij hjk b
      exact (Nat.decreasingInduction_trans (motive := fun m (_ : m ≤ k) => B m)
        hij hjk (fun m _ => step m) b).symm)
    (fun _ _ => Set.toFinite _)
  refine ⟨fun m hm => a m hm, ?_⟩
  intro m hm
  have h := congrFun (ha (Nat.le_succ m)) hm
  simpa only [π, Nat.decreasingInduction_succ', step] using h

/-- The `1 - shift` map of an inverse sequence of finite abelian groups is
surjective, the algebraic vanishing criterion for its first derived limit.
For each target sequence, apply finite inverse-system compactness to the
affine restrictions; the original homomorphisms need not be surjective. -/
private theorem surjective_sub_shift_of_finite (A : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Finite (A n)]
    (f : ∀ n, A (n + 1) →+ A n) :
    Function.Surjective (fun x : ∀ n, A n => fun n => x n - f n (x (n + 1))) := by
  intro b
  obtain ⟨x, hx⟩ := exists_compatible_of_finite 0 (fun n _ => A n)
    (fun n _ a => b n + f n a) (fun n _ => inferInstance)
    (fun n _ => ⟨0⟩)
  refine ⟨fun n => x n (Nat.zero_le n), ?_⟩
  funext n
  have h := hx n (Nat.zero_le n)
  dsimp only at h ⊢
  rw [← h, add_sub_cancel_right]


private theorem finite_fiber_of_finite_ker
    {A : Type u} {B : Type v} [AddGroup A] [AddGroup B]
    (f : A →+ B) [Finite f.ker] (b : B) : Finite {a : A // f a = b} := by
  classical
  by_cases h : Nonempty {a : A // f a = b}
  · let a₀ := Classical.choice h
    let e : {a : A // f a = b} → f.ker := fun a =>
      ⟨a.val - a₀.val, by simp only [AddMonoidHom.mem_ker, map_sub, a.property, a₀.property, sub_self]⟩
    exact Finite.of_injective e (fun a a' h => Subtype.ext (sub_left_inj.mp (congrArg Subtype.val h)))
  · letI : IsEmpty {a : A // f a = b} := not_nonempty_iff.mp h
    infer_instance

private theorem finite_fiber_comp
    {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B)
    (hf : ∀ c, Finite {b // f b = c}) (hg : ∀ b, Finite {a // g a = b})
    (c : C) : Finite {a // f (g a) = c} := by
  letI : Finite {b // f b = c} := hf c
  letI : ∀ b : {b // f b = c}, Finite {a // g a = b.val} := fun b => hg b.val
  let e : {a // f (g a) = c} → Σ b : {b // f b = c}, {a // g a = b.val} :=
    fun a => ⟨⟨g a.val, a.property⟩, ⟨a.val, rfl⟩⟩
  exact Finite.of_injective e (fun a a' h => Subtype.ext (congrArg (fun z => z.2.val) h))


private theorem finite_fiber_tower
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (p : ∀ a b, a ≤ b → G b →+ G a)
    (pid : ∀ a x, p a a (Nat.le_refl a) x = x)
    (pcomp : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c) x,
      p a b hab (p b c hbc x) = p a c (hab.trans hbc) x)
    (hfinite : ∀ n, Finite (p n (n+1) (Nat.le_succ n)).ker)
    (a b : ℕ) (hab : a ≤ b) (x : G a) : Finite {y : G b // p a b hab y = x} := by
  induction b, hab using Nat.le_induction generalizing x with
  | base =>
    let he : {y : G a // p a a (Nat.le_refl a) y = x} → {y : G a // y = x} :=
      fun y => ⟨y.val, (pid a y.val).symm.trans y.property⟩
    exact Finite.of_injective he (by
      intro y y' h
      apply Subtype.ext
      exact congrArg (fun z : {y : G a // y = x} => z.val) h)
  | succ b hab ih =>
    letI := hfinite b
    have hf : ∀ z, Finite {y : G b // p a b hab y = z} := by
      intro z
      exact ih z
    have hg := finite_fiber_comp (p a b hab) (p b (b+1) (Nat.le_succ b)) hf
      (finite_fiber_of_finite_ker (p b (b+1) (Nat.le_succ b))) x
    exact Finite.of_injective
      (fun y : {y : G (b+1) // p a (b+1) (hab.trans (Nat.le_succ b)) y = x} =>
        (⟨y.val, (pcomp a b (b+1) hab (Nat.le_succ b) y.val).trans y.property⟩ :
          {y : G (b+1) // p a b hab (p b (b+1) (Nat.le_succ b) y) = x}))
      (by
        intro y y' h
        apply Subtype.ext
        exact congrArg (fun z : {y : G (b+1) // p a b hab (p b (b+1) (Nat.le_succ b) y) = x} => z.val) h)


/-- A zero inverse limit together with finite adjacent kernels separates all image filtrations. -/
private theorem separated_of_finite_ker
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (p : ∀ a b, a ≤ b → G b →+ G a)
    (pid : ∀ a x, p a a (Nat.le_refl a) x = x)
    (pcomp : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c) x,
      p a b hab (p b c hbc x) = p a c (hab.trans hbc) x)
    (hfinite : ∀ n, Finite (p n (n+1) (Nat.le_succ n)).ker)
    (hzero : ∀ z : ∀ n, G n,
      (∀ n, p n (n+1) (Nat.le_succ n) (z (n+1)) = z n) → ∀ n, z n = 0)
    (a : ℕ) (x : G a)
    (hx : ∀ b (hab : a ≤ b), ∃ y, p a b hab y = x) : x = 0 := by
  classical
  let A (b : ℕ) (hab : a ≤ b) := {y : G b // p a b hab y = x}
  let step (b : ℕ) (hab : a ≤ b) : A (b+1) (Nat.le_succ_of_le hab) → A b hab :=
    fun y => ⟨p b (b+1) (Nat.le_succ b) y.val,
      (pcomp a b (b+1) hab (Nat.le_succ b) y.val).trans y.property⟩
  obtain ⟨u, hu⟩ := exists_compatible_of_finite a A step
    (fun b hab => finite_fiber_tower G p pid pcomp hfinite a b hab x)
    (fun b hab => let ⟨y, hy⟩ := hx b hab; ⟨⟨y, hy⟩⟩)
  have hua : (u a (Nat.le_refl a)).val = x :=
    (pid a _).symm.trans (u a (Nat.le_refl a)).property
  let z (b : ℕ) : G b := if hab : a ≤ b then (u b hab).val else p b a (by omega) x
  have hcompat : ∀ b, p b (b+1) (Nat.le_succ b) (z (b+1)) = z b := by
    intro b
    by_cases hab : a ≤ b
    · have hab' : a ≤ b+1 := Nat.le_succ_of_le hab
      simp only [z, dif_pos hab, dif_pos hab']
      exact congrArg Subtype.val (hu b hab)
    · by_cases hab' : a ≤ b+1
      · have hba : b+1 = a := by omega
        subst a
        simp only [z, dif_pos hab', dif_neg hab]
        rw [hua]
      · simp only [z, dif_neg hab, dif_neg hab']
        exact pcomp b (b+1) a (Nat.le_succ b) (by omega) x
  have hza := hzero z hcompat a
  simpa only [z, dif_pos (Nat.le_refl a), hua] using hza

/-- Injectivity of the explicit difference operator kills compatible families. -/
private theorem compatible_zero_of_difference_injective
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (step : ∀ n, G (n+1) →+ G n)
    (hinj : Function.Injective (fun z : ∀ n, G n => fun n => z n - step n (z (n+1))))
    (z : ∀ n, G n) (hz : ∀ n, step n (z (n+1)) = z n) : ∀ n, z n = 0 := by
  have he : z = 0 := hinj (by funext n; simp only [hz, sub_self, Pi.zero_apply, map_zero])
  intro n
  exact congrFun he n



/-- The correction step in §9.1: solving the difference equation changes
compatible representatives into one representative of all quotient classes. -/
private theorem common_representative
    (G : ℕ → Type v) [∀ s, AddCommGroup (G s)]
    {A : Type w} [AddCommGroup A]
    (i : ∀ s, G (s+1) →+ G s) (p : ∀ s, G s →+ A)
    (hp : ∀ s y, p s (i s y) = p (s+1) y)
    (hdelta : Function.Surjective (fun z : ∀ s, G s => fun s => z s - i s (z (s+1))))
    (x : ℕ → A) (hx : ∀ s, ∃ y, p s y = x s - x (s+1)) :
    ∃ a : A, ∀ s, ∃ y, p s y = x s - a := by
  classical
  choose y hy using hx
  obtain ⟨z, hz⟩ := hdelta y
  have hz' (s : ℕ) : p s (z s) - p (s+1) (z (s+1)) = x s - x (s+1) := by
    have h := congrArg (p s) (congrFun hz s)
    simpa only [map_sub, hp, hy] using h
  have hw (s : ℕ) : x s - p s (z s) = x 0 - p 0 (z 0) := by
    induction s with
    | zero => rfl
    | succ s ih =>
      calc
        x (s+1) - p (s+1) (z (s+1)) = x s - p s (z s) := by
          rw [sub_eq_iff_eq_add.mp (hz' s)]
          abel
        _ = _ := ih
  refine ⟨x 0 - p 0 (z 0), fun s => ⟨z s, ?_⟩⟩
  rw [← hw s]
  abel


end KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
