module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Presentation.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

/-- The fixed computed square is genuinely the product of computed h₆ with
itself, relative to the existing E₂ presentation. No survival is asserted. -/
theorem computedH6_mul_self :
    linE2Presentation.product 1 64 1 64 computedH6 computedH6 = computedH6Square := by
  apply linToSphere_product_eq (s := 1) (t := 64) (s' := 1) (t' := 64)
    (by decide) KIP126.LinE2.dataH6 KIP126.LinE2.dataH6 KIP126.LinE2.dataH6Sq
  change _ * _ = _ ^ 2
  exact (pow_two _).symm

end KIP126.Classical.Adams
