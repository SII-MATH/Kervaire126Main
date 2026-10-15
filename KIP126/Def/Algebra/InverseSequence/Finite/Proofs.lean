module

public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Finite.Prod
public import Mathlib.Order.KonigLemma
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Basic

@[expose] public section

namespace KIP126.Algebra.InverseSequence

universe u

/-- Nonempty finite terms with arbitrary adjacent restriction maps admit a
compatible dependent inverse sequence. The point at the initial index is
not prescribed, and the restriction maps need not be surjective. -/
theorem exists_compatible_of_finite (m₀ : ℕ)
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
theorem surjective_sub_shift_of_finite (A : ℕ → Type u)
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

end KIP126.Algebra.InverseSequence
