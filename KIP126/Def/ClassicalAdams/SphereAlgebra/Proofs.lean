module

public import KIP126.Def.ClassicalAdams.SphereAlgebra.Data
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Components.Proofs

@[expose] public section


/-! Canonical inclusions and the distributive product on the specified E₂ direct sum. -/

namespace KIP126.Classical.Adams.Sphere.Algebra

open KIP126.Algebra
noncomputable section

variable {Q : KIP126.StableHomotopy.Spectra.CompletionModel} (c : KIP126.HF2AdamsContext Q)

attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product

/-- Distinct actual classes of a fixed bidegree remain distinct in the direct sum. -/
theorem embed_injective (p : ℕ × ℕ) : Function.Injective ((embed c) p) :=
  DirectSum.of_injective (β := (ActualE2At c)) p

/-- The direct-sum multiplication extends exactly the fixed page product. -/
theorem embed_product (p q : ℕ × ℕ) (x : (ActualE2At c) p) (y : (ActualE2At c) q) :
    (embed c) (p + q) ((actualE2Product c) p q x y) = (embed c) p x * (embed c) q y := by
  exact (DirectSum.of_mul_of x y).symm

/-- The distinguished global class is the inclusion of the actual sphere identity. -/
theorem embed_unit : (embed c) 0 (actualE2Unit c) = (1 : (ActualE2Total c)) :=
  (DirectSum.one_def (ActualE2At c)).symm

end
end KIP126.Classical.Adams.Sphere.Algebra
