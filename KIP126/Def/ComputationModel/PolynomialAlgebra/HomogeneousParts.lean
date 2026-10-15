module

public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

/-! Homogeneous monomial spans in a polynomial quotient. The generators, their
bidegrees and the ideal are arbitrary; no imported coordinate table is selected. -/
namespace KIP126.Algebra.PolynomialCoordinates
open MvPolynomial
universe u
variable {ι : Type u} [DecidableEq ι]

/-- Bidegree of a monomial for an arbitrary generator-degree assignment. -/
def monomialDegree (degree : ι → ℕ × ℕ) (m : ι →₀ ℕ) : ℕ × ℕ :=
  m.sum fun i a => (a * (degree i).1, a * (degree i).2)

/-- The span of projected monomials of a given bidegree. This construction
requires no homogeneity assertion about the ideal. -/
noncomputable def homogeneousPart (degree : ι → ℕ × ℕ)
    (I : Ideal (MvPolynomial ι F2)) (s t : ℕ) : Submodule F2 (MvPolynomial ι F2 ⧸ I) :=
  Submodule.span F2 {x | ∃ m : ι →₀ ℕ,
    monomialDegree degree m = (s,t) ∧ x = Ideal.Quotient.mk I (MvPolynomial.monomial m 1)}

variable (degree : ι → ℕ × ℕ) (I : Ideal (MvPolynomial ι F2))

theorem monomialDegree_add (m n : ι →₀ ℕ) :
    monomialDegree degree (m+n) = monomialDegree degree m + monomialDegree degree n := by
  unfold monomialDegree
  exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])

theorem multiply_mem {s t s' t' : ℕ} {a b : MvPolynomial ι F2 ⧸ I}
    (ha : a ∈ homogeneousPart degree I s t) (hb : b ∈ homogeneousPart degree I s' t') :
    a*b ∈ homogeneousPart degree I (s+s') (t+t') := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := ha
      obtain ⟨n, hn, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨m+n, ?_, ?_⟩
      · simpa [hm, hn] using monomialDegree_add degree m n
      · simp [← map_mul, MvPolynomial.monomial_mul]
    | zero => simp
    | add b c _ _ hb hc =>
      simpa [mul_add] using (homogeneousPart degree I (s+s') (t+t')).add_mem hb hc
    | smul r b _ hb =>
      simpa [mul_smul_comm] using (homogeneousPart degree I (s+s') (t+t')).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc =>
    simpa [add_mul] using (homogeneousPart degree I (s+s') (t+t')).add_mem ha hc
  | smul r a _ ha =>
    simpa [smul_mul_assoc] using (homogeneousPart degree I (s+s') (t+t')).smul_mem r ha

theorem one_mem : (1 : MvPolynomial ι F2 ⧸ I) ∈ homogeneousPart degree I 0 0 := by
  apply Submodule.subset_span
  refine ⟨0, ?_, ?_⟩
  · simp only [monomialDegree, Finsupp.sum_zero_index]
    rfl
  · simp

theorem generator_pow_mem (i : ι) (n : ℕ) :
    (Ideal.Quotient.mk I (MvPolynomial.X i)) ^ n ∈ homogeneousPart degree I
      (n * (degree i).1) (n * (degree i).2) := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single i n, ?_, ?_⟩
  · simp [monomialDegree]
  · simp [← map_pow, MvPolynomial.X_pow_eq_monomial]

end KIP126.Algebra.PolynomialCoordinates
