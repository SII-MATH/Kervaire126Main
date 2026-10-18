module

import all KIP126.SpectralSequence.Completion.Predicates

@[expose] section

/-!
# Basic completion proofs

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-! ### Completion of filtered objects -/

noncomputable instance Filtration.hasLimitCompletionFunctor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    HasLimit (fil.completionFunctor hbb k) := inferInstance

lemma Filtration.completionProj'_factor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s : ℤ) :
    fil.completionProj' hbb k (s + 1) ≫ fil.truncationTransition (show s ≤ s + 1 by omega) k =
    fil.completionProj' hbb k s := by
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s - hbb.lo k).toNat ≤ (s + 1 - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
  all_goals simp only [Opposite.unop_op]
  · rfl
  · omega

/-! ### Mittag-Leffler condition -/

-- Keep the original instance parameters of this theorem.
set_option linter.unusedSectionVars false in
/-- Bounded-above filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBoundedAbove.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hba : fil.IsBoundedAbove) : fil.IsMittagLeffler :=
  hba.isMittagLeffler

/-- Bounded filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBounded.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsMittagLeffler :=
  hb.toIsBoundedAbove.toIsMittagLeffler

end KIP126.Core.SpectralSequence
