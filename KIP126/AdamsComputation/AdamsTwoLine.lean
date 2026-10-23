module

public import KIP126.Literature

/-! The unbounded Ext² basis input, independently of any later Adams page.
This is not inferred by extrapolating the bounded computation archive. -/
@[expose] section
namespace KIP126.AdamsComputation
open CategoryTheory KIP126.Classical.Adams
open KIP126.AdamsSynthetic.Standard (model)

/-- Every nonzero homogeneous second-line element is a standard product.
The degree equation and equality are in the actual fixed E₂ module. -/
public theorem two_line_exhaustive (t : ℤ) (x : model.classical.sphere.Page 2 (2,t))
    (hx : x ≠ 0) :
    ∃ i j : ℕ, i ≤ j ∧
      ∃ degree : hiDegree i + hiDegree j = (2,t),
        x = (eqToHom (congrArg (ActualE2At model.classical) degree))
          (KIP126.Literature.Standard.hiProduct i j) := by
  sorry

end KIP126.AdamsComputation
