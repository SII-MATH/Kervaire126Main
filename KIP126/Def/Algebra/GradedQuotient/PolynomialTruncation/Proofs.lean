module

public import KIP126.Def.Algebra.GradedQuotient.PolynomialTruncation.Data

@[expose] public section


/-! Artificial truncation does not change components below its cutoff. -/
namespace KIP126.Algebra.PolynomialTruncation
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] (w : σ → ℕ × ℕ)

theorem highIdeal_coeff_zero (N : ℕ) {p : MvPolynomial σ R} (hp : p ∈ highIdeal w N) :
    ∀ m : σ →₀ ℕ, (Finsupp.weight w m).2 ≤ N → coeff m p = 0 := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n, hn, rfl⟩ := hp
    intro m hm
    have hne : n ≠ m := by intro h; subst n; omega
    simp [coeff_monomial, hne]
  | zero => simp
  | add p q _ _ hp hq =>
    intro m hm
    simp only [coeff_add, hp m hm, hq m hm, add_zero]
  | smul r p _ hp =>
    intro m hm
    change coeff m (r*p) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a,b⟩ hab
    have he : a + b = m := by simpa using hab
    have hb : (Finsupp.weight w b).2 ≤ N := by
      have hw := congrArg Prod.snd (congrArg (Finsupp.weight w) he)
      simp only [map_add, Prod.snd_add] at hw
      omega
    simp [hp b hb]

theorem low_component_highIdeal (N : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ highIdeal w N) (d : ℕ × ℕ) (hd : d.2 ≤ N) :
    weightedHomogeneousComponent w d p = 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hm
  · exact highIdeal_coeff_zero w N hp m (hm ▸ hd)
  · rfl

local instance : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule R w) :=
  MvPolynomial.weightedGradedAlgebra R w

/-- Homogeneous elements below the cutoff belong to the larger ideal exactly
when they already belong to the original homogeneous ideal. -/
theorem low_mem_sup_iff (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule R w))
    (N : ℕ) {p : MvPolynomial σ R} {d : ℕ × ℕ}
    (hp : p.IsWeightedHomogeneous w d) (hd : d.2 ≤ N) :
    p ∈ I ⊔ highIdeal w N ↔ p ∈ I := by
  constructor
  · intro h
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h
    have he := congrArg (weightedHomogeneousComponent w d) hij
    rw [map_add, low_component_highIdeal w N hj d hd, add_zero,
      hp.weightedHomogeneousComponent_same] at he
    rw [← he]
    exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R w hI hi d
  · exact fun h => (show I ≤ I ⊔ highIdeal w N from le_sup_left) h

end
end KIP126.Algebra.PolynomialTruncation
