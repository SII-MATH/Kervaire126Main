module

public import KIP126.Computation.WellFormedness.LinCoordinates.RelationAlgebra.Grading

@[expose] public section

namespace KIP126.LinE2
open KIP126.Algebra MvPolynomial
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : GradedAlgebra (weightedHomogeneousSubmodule F2 generatorDegree) :=
  weightedGradedAlgebra F2 generatorDegree

/-- The homogeneous component of the relation algebra is the span of monomials
of the same bidegree. -/
theorem relationHomogeneousPart_eq_span (s t : ℕ) :
    relationHomogeneousPart s t = Submodule.span F2
      {x | ∃ m : Generator →₀ ℕ, monomialDegree m = (s,t) ∧
        x = relationProjection (MvPolynomial.monomial m 1)} := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq => simpa only [map_add] using
        (Submodule.span F2 _).add_mem ihp ihq
    | monomial m r hm =>
      have hb : relationProjection (MvPolynomial.monomial m (1 : F2)) ∈ Submodule.span F2
          {x | ∃ m : Generator →₀ ℕ, monomialDegree m = (s,t) ∧
            x = relationProjection (MvPolynomial.monomial m 1)} :=
        Submodule.subset_span ⟨m, (weight_generatorDegree m).symm.trans hm, rfl⟩
      have hh := (Submodule.span F2 _).smul_mem r hb
      simp only [← map_smul, smul_eq_mul, mul_one] at hh
      exact hh
  · apply Submodule.span_le.mpr
    rintro x ⟨m, hm, rfl⟩
    exact ⟨MvPolynomial.monomial m 1,
      MvPolynomial.isWeightedHomogeneous_monomial generatorDegree m 1
        ((weight_generatorDegree m).trans hm), rfl⟩

@[simp] theorem truncateAtEquiv_apply_val (s t : ℕ) (ht : t ≤ 261) (x : RelationAt s t) :
    (truncateAtEquiv s t ht x).val = truncate x.val := rfl

@[simp] theorem truncateAtEquiv_symm_apply (s t : ℕ) (ht : t ≤ 261) (x : E2At s t) :
    truncate ((truncateAtEquiv s t ht).symm x).val = x.val := by
  exact congrArg Subtype.val ((truncateAtEquiv s t ht).apply_symm_apply x)

/-- Every original relation vanishes in the untruncated algebra. -/
theorem relation_csv_relation_zero (code : String) (h : code ∈ RawData.relations) :
    relationProjection (relationPolynomial code) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨code, h, rfl⟩)


/-- The low-degree inverse identifies products whenever the product degree is covered. -/
theorem truncateAtEquiv_mul {s t s' t' : ℕ} (ht : t+t' ≤ 261)
    (x : RelationAt s t) (y : RelationAt s' t') :
    (truncateAtEquiv (s+s') (t+t') ht (relationMultiply x y)).val =
      (truncateAtEquiv s t (by omega) x).val *
        (truncateAtEquiv s' t' (by omega) y).val := map_mul truncate x.val y.val


end
end KIP126.LinE2
