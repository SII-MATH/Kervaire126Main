module

public import KIP126.Def.ClassicalAdams.SphereAlgebra.Components.Data

@[expose] public section


/-! The direct sum of the specified sphere E₂ page with its distributive
product. Both the product and the specified identity class are fixed before
the native comparison, in every bidegree. -/

namespace KIP126.Classical.Adams.Sphere.Algebra

open KIP126.Algebra
noncomputable section

variable {Q : KIP126.StableHomotopy.Spectra.CompletionModel} (c : KIP126.HF2AdamsContext Q)

attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product

instance actualE2GradedNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (ActualE2At c) where
  mul := fun {p q} x y => (actualE2Product c) p q x y
  mul_zero := fun x => map_zero ((actualE2Product c) _ _ x)
  zero_mul := fun x => by simp
  mul_add := fun x y z => map_add ((actualE2Product c) _ _ x) y z
  add_mul := fun x y z => by simp

/-- All nonnegative homogeneous pieces of the specified sphere E₂,
with finite support and the fixed multiplication. No product is truncated. -/
abbrev ActualE2Total := DirectSum (ℕ × ℕ) (ActualE2At c)

/-- The canonical linear inclusion of one actual page component. -/
def embed (p : ℕ × ℕ) : (ActualE2At c) p →ₗ[F2] (ActualE2Total c) :=
  DirectSum.lof F2 (ℕ × ℕ) (ActualE2At c) p

end
end KIP126.Classical.Adams.Sphere.Algebra
