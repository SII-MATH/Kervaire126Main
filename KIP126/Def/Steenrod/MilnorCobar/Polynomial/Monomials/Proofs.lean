module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Predicates
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra MvPolynomial
open scoped Classical

/-- Augmentation deletes precisely the monomials using the specified slot. -/
theorem augmentSlot_monomial {s : ℕ} (slot : Fin s) (d : (Fin s × ℕ) →₀ ℕ)
    (r : F2) : augmentSlot slot (monomial d r) =
      if UsesSlot d slot then 0 else monomial d r := by
  classical
  by_cases h : UsesSlot d slot
  · rw [if_pos h, augmentSlot, aeval_monomial, Finsupp.prod]
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hj), mul_zero]
    simp [zero_pow hj]
  · rw [if_neg h, augmentSlot, aeval_monomial, monomial_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    have hne : a.1 ≠ slot := by
      intro heq
      apply h
      exact ⟨a.2, by simpa [← heq] using Finsupp.mem_support_iff.mp ha⟩
    simp [hne]

/-- No cancellation among different monomials is introduced by augmentation. -/
theorem coeff_augmentSlot {s : ℕ} (slot : Fin s) (d : (Fin s × ℕ) →₀ ℕ)
    (x : TensorPower s) :
    coeff d (augmentSlot slot x) = if UsesSlot d slot then 0 else coeff d x := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [augmentSlot_monomial]
    by_cases he : e = d
    · subst e
      split_ifs <;> simp
    · by_cases hu : UsesSlot e slot <;> by_cases hd : UsesSlot d slot <;>
        simp [hu, hd, coeff_monomial, he]
  | add x y hx hy =>
    simp only [map_add, coeff_add, hx, hy]
    split_ifs <;> simp

theorem augmentSlot_eq_zero_iff {s : ℕ} (slot : Fin s) (x : TensorPower s) :
    augmentSlot slot x = 0 ↔ ∀ d, coeff d x ≠ 0 → UsesSlot d slot := by
  classical
  constructor
  · intro hx d hd
    by_contra hu
    have h := congrArg (coeff d) hx
    rw [coeff_augmentSlot, if_neg hu, coeff_zero] at h
    exact hd h
  · intro hx
    ext d
    rw [coeff_augmentSlot, coeff_zero]
    split_ifs with hu
    · rfl
    · exact not_not.mp (mt (hx d) hu)

/-- The two defining submodule conditions are exactly a monomial-support condition. -/
theorem mem_cochains_iff_monomials {s t : ℕ} (x : TensorPower s) :
    x ∈ cochains s t ↔ ∀ d, coeff d x ≠ 0 → IsCochainMonomial t d := by
  constructor
  · rintro ⟨hw, hn⟩ d hd
    refine ⟨hw hd, fun slot => ?_⟩
    have hslot : augmentSlot slot x = 0 := (Submodule.mem_iInf _).mp hn slot
    exact (augmentSlot_eq_zero_iff slot x).mp hslot d hd
  · intro hx
    refine ⟨fun d hd => (hx d hd).1, (Submodule.mem_iInf _).mpr fun slot => ?_⟩
    exact (augmentSlot_eq_zero_iff slot x).mpr fun d hd => (hx d hd).2 slot

theorem monomial_mem_cochains {s t : ℕ} (d : (Fin s × ℕ) →₀ ℕ)
    (hd : IsCochainMonomial t d) (r : F2) : monomial d r ∈ cochains s t := by
  classical
  apply (mem_cochains_iff_monomials _).mpr
  intro e he
  by_cases h : d = e
  · simpa [← h] using hd
  · exact (he (by simp [coeff_monomial, h])).elim

/-- Taking coefficients sends the existing cochain submodule exactly onto
the finitely supported functions on normalized homogeneous exponents. -/
theorem cochains_map_coeff (s t : ℕ) :
    (cochains s t).map (AddMonoidAlgebra.coeffLinearEquiv F2).toLinearMap =
      Finsupp.supported F2 F2 {d | IsCochainMonomial t d} := by
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (Finsupp.mem_supported _ _).mpr
    intro d hd
    exact (mem_cochains_iff_monomials x).mp hx d (Finsupp.mem_support_iff.mp hd)
  · intro hf
    refine ⟨(AddMonoidAlgebra.coeffLinearEquiv F2).symm f, ?_,
      (AddMonoidAlgebra.coeffLinearEquiv F2).apply_symm_apply f⟩
    apply (mem_cochains_iff_monomials _).mpr
    intro d hd
    exact (Finsupp.mem_supported _ _).mp hf (Finsupp.mem_support_iff.mpr hd)

end

end KIP126.Steenrod.Milnor
