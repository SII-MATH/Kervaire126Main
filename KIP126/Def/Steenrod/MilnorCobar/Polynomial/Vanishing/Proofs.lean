module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

/-- Tensor length zero has no variables, so a cochain of nonzero internal
degree is zero. This is a polynomial fact, independent of a spectrum model. -/
theorem cochains_zero_length_subsingleton (t : ℕ) (ht : t ≠ 0) :
    Subsingleton (cochains 0 t) := by
  have hz (x : cochains 0 t) : x = 0 := by
    apply Subtype.ext
    change x.val = 0
    by_contra h
    exact ht (MvPolynomial.IsWeightedHomogeneous.inj_right h x.property.1
      (MvPolynomial.isWeightedHomogeneous_of_isEmpty
        (R := KIP126.Algebra.F2) weight x.val))
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end KIP126.Steenrod.Milnor
