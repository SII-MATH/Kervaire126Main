module

public import KIP126.Def.ClassicalAdams.SphereAlgebra.Components.Data

@[expose] public section


/-! The specified E₂ product agrees with its cobar definition and respects
the scalar action. These facts use the specified bilinear product directly. -/

namespace KIP126.Classical.Adams.Sphere.Algebra

open KIP126.Algebra
noncomputable section

variable {Q : KIP126.StableHomotopy.Spectra.CompletionModel} (c : KIP126.HF2AdamsContext Q)

set_option maxHeartbeats 1200000 in
/-- Bundling F₂-linearity does not replace the existing actual product. -/
theorem actualE2Product_apply (p q : ℕ × ℕ) (x : (ActualE2At c) p) (y : (ActualE2At c) q) :
    (actualE2Product c) p q x y =
      KIP126.Classical.Adams.Sphere.Internal.product c.foundation.hf2 c.milnor
        (s := p.1) (t := p.2) (s' := q.1) (t' := q.2) x y := rfl

-- Avoid elaborator reduction through the fixed stable homotopy category when
-- checking elementary identities of the already bundled linear maps.
attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product
  actualE2ToCobar actualE2ToCobarInt

/-- Scalar multiplication in the first factor follows from the existing
bilinear map, before any multiplicative structural laws are used. -/
theorem actualE2_smul_mul (r : F2) (a b : GradedMonoid (ActualE2At c)) :
    (r • a) * b = r • (a * b) := by
  obtain ⟨p, x⟩ := a
  obtain ⟨q, y⟩ := b
  exact Sigma.ext rfl
    (heq_of_eq (LinearMap.congr_fun (((actualE2Product c) p q).map_smul r x) y))

end
end KIP126.Classical.Adams.Sphere.Algebra
