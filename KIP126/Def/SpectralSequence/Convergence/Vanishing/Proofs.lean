module

public import KIP126.Def.SpectralSequence.Convergence.Proofs
public import KIP126.Def.Algebra.Completion.Data
public import KIP126.Def.Algebra.Filtration.Data
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Vanishing of associated grades raises the filtration of the same
object. This extracts the filtration argument from the historical Adams
divisibility proof without importing its Adams objects or assumptions. -/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ω : Type w} {A : ω → C} (F : Filtration A)

/-- A zero associated grade identifies adjacent filtration subobjects. -/
theorem Filtration.eq_succ_of_associatedGraded_isZero (s : ℤ) (k : ω)
    (h : IsZero (F.associatedGraded s k)) : F.F s k = F.F (s + 1) k := by
  let i := Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k)
  haveI : Epi i := Abelian.epi_of_cokernel_π_eq_zero i (h.eq_of_tgt _ _)
  haveI : IsIso i := isIso_of_mono_of_epi i
  apply le_antisymm
  · apply Subobject.le_of_comm (inv i)
    rw [← Subobject.ofLE_arrow (F.mono s k)]
    exact IsIso.inv_hom_id_assoc i _
  · exact F.mono s k

/-- Vanishing on a finite interval identifies its endpoint filtrations.
No separation or convergence hypothesis is required. -/
theorem Filtration.eq_of_associatedGraded_isZero (s t : ℤ) (k : ω)
    (hst : s ≤ t)
    (h : ∀ j : ℤ, s ≤ j → j < t → IsZero (F.associatedGraded j k)) :
    F.F s k = F.F t k := by
  have step : ∀ n : ℕ, s + n ≤ t → F.F s k = F.F (s + n) k := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show s + ((n + 1 : ℕ) : ℤ) = (s + n) + 1 by omega]
      exact (ih (by omega)).trans
        (F.eq_succ_of_associatedGraded_isZero _ k (h _ (by omega) (by omega)))
  simpa only [show s + ((t - s).toNat : ℤ) = t by omega] using
    step (t - s).toNat (by omega)

end KIP126.SpectralSequence
