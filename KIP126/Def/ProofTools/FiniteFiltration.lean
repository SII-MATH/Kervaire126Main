module

public import KIP126.Def.SpectralSequence

/-! Finite filtration arguments from the proof of the paper's stretching
criterion. Migrated with their proofs from KIP126/Def/Kervaire/Route/Tools/
PageExtensionStretching/Proofs.lean at bbac1fc05843 (MIT; see the retained source LICENSE).
No infinite-completion statement follows from these finite arguments. -/

@[expose] section
namespace KIP126.ProofTools

/-- A finite correction argument with the actual residual kept throughout. -/
public theorem finite_filtration_correction
    {A A' B : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
    (ρ : A' →+ A) (g : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup A')
    (T : AddSubgroup B) (hL : Antitone L)
    (s : ℤ) (N : ℕ)
    (hstep : ∀ k : ℤ, s ≤ k → k < s + N → ∀ δ : A, δ ∈ E k →
      (∃ ε : A', ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)) ∨ g δ ∈ T)
    (hend : ∀ δ : A, δ ∈ E (s + N) → g δ ∈ T)
    (α₀ : A) (α : A') (hδ : α₀ - ρ α ∈ E s) :
    ∃ α' : A', α' - α ∈ L s ∧ g (α₀ - ρ α') ∈ T := by
  induction N generalizing s α with
  | zero =>
    refine ⟨α, ?_, hend _ ?_⟩
    · simpa only [sub_self] using (L s).zero_mem
    · simpa only [Nat.cast_zero, add_zero] using hδ
  | succ N ih =>
    rcases hstep s le_rfl (by omega) _ hδ with hcorrect | hstop
    · obtain ⟨ε, hε, hδε⟩ := hcorrect
      have hδ' : α₀ - ρ (α + ε) ∈ E (s + 1) := by
        simpa only [map_add, sub_add_eq_sub_sub] using hδε
      obtain ⟨α', hα', hfinal⟩ := ih (s + 1)
        (fun k hk hkn δ hδ => hstep k (by omega) (by omega) δ hδ)
        (fun δ hδ => hend δ (by simpa only [Nat.cast_succ, add_assoc,
          add_comm, add_left_comm] using hδ)) (α + ε) hδ'
      refine ⟨α', ?_, hfinal⟩
      have hmem := (L s).add_mem (hL (by omega) hα') hε
      convert hmem using 1
      abel
    · exact ⟨α, by simpa only [sub_self] using (L s).zero_mem, hstop⟩


/-- Injectivity of successive graded maps reflects membership through a finite
filtration interval; it does not require injectivity of the ambient map. -/
public theorem finite_filtration_reflection
    {B' B : Type*} [AddCommGroup B'] [AddCommGroup B]
    (ρ : B' →+ B) (L : ℤ → AddSubgroup B') (E : ℤ → AddSubgroup B)
    (hE : Antitone E) (s : ℤ) (N : ℕ)
    (hgraded : ∀ k : ℤ, s ≤ k → k < s + N → ∀ b : B', b ∈ L k →
      ρ b ∈ E (k + 1) → b ∈ L (k + 1))
    (b : B') (hb : b ∈ L s) (hρb : ρ b ∈ E (s + N)) :
    b ∈ L (s + N) := by
  have h : ∀ k : ℕ, k ≤ N → b ∈ L (s + k) := by
    intro k hk
    induction k with
    | zero => simpa only [Nat.cast_zero, add_zero] using hb
    | succ k ih =>
      have hkN : k ≤ N := by omega
      have hnext := hgraded (s + k) (by omega) (by omega) b (ih hkN)
        (hE (by omega) hρb)
      simpa only [Nat.cast_succ, add_assoc] using hnext
  exact h N le_rfl

/-- Failure to lie in the final layer is witnessed by a nonzero leading grade
in the finite interval. -/
public theorem first_nonzero_filtration_grade
    {B : Type*} [AddCommGroup B] (E : ℤ → AddSubgroup B)
    (s : ℤ) (N : ℕ) (b : B) (hb : b ∈ E s) (hnot : b ∉ E (s + N)) :
    ∃ k : ℤ, s ≤ k ∧ k < s + N ∧ b ∈ E k ∧ b ∉ E (k + 1) := by
  induction N generalizing s with
  | zero => exact (hnot (by simpa only [Nat.cast_zero, add_zero] using hb)).elim
  | succ N ih =>
    by_cases hnext : b ∈ E (s + 1)
    · have hnot' : b ∉ E ((s + 1) + N) := by
        simpa only [Nat.cast_succ, add_assoc, add_comm, add_left_comm] using hnot
      obtain ⟨k, hk, hkN, hb, hnot⟩ := ih (s + 1) hnext hnot'
      exact ⟨k, by omega, by omega, hb, hnot⟩
    · exact ⟨s, le_rfl, by omega, hb, hnext⟩


end KIP126.ProofTools
