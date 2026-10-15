module

public import KIP126.Computation.WellFormedness.LinCoordinates.E2
public import KIP126.Def.Algebra.TwoElement.Proofs

@[expose] public section

namespace KIP126.LinE2

theorem monomialDegree_add (m n : Generator →₀ ℕ) :
    monomialDegree (m+n) = monomialDegree m + monomialDegree n :=
  KIP126.Algebra.PolynomialCoordinates.monomialDegree_add generatorDegree m n

/-- Every archived relation holds by construction of the quotient. -/
theorem csv_relation_zero (code : String) (h : code ∈ RawData.relations) :
    projection (relationPolynomial code) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  exact Ideal.subset_span (Or.inl ⟨code, h, rfl⟩)

theorem h6Generator_name : (RawData.generators[h6Generator.val]!).1 = "h_6" := by
  simp [RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk2, RawData.generatorCount, h6Generator,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

/-- Exhaust an entire homogeneous component from its singleton-span equality.
The span equality must be proved separately; no basis or differential is assumed. -/
theorem E2At_eq_zero_or_of_span {s t : ℕ} (a : E2At s t)
    (hspan : homogeneousPart s t =
      Submodule.span KIP126.Algebra.F2 ({a.val} : Set E2)) (x : E2At s t) :
    x = 0 ∨ x = a := by
  have hx : x.val ∈ Submodule.span KIP126.Algebra.F2 ({a.val} : Set E2) :=
    (le_of_eq hspan) x.property
  rcases KIP126.Algebra.eq_zero_or_of_span_singleton a.val x.val hx with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)


end KIP126.LinE2
