module

public import KIP126.Computation.WellFormedness.LinCoordinates.E2
public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

namespace KIP126.LinE2

/-- Every archived relation holds by construction of the quotient. -/
theorem csv_relation_zero (code : String) (h : code ∈ RawData.relations) :
    projection (relationPolynomial code) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  exact Ideal.subset_span (Or.inl ⟨code, h, rfl⟩)

end KIP126.LinE2
