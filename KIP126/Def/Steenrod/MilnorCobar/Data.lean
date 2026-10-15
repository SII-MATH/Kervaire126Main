module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Proofs

@[expose] public section

/-!
# Normalized Milnor cobar data

Restrict the specified polynomial operations using the lower-layer
preservation theorems, then form the standard cochains. No theorem or
proof placeholder is declared in this data module.
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra

/-- The actual normalized cobar differential. -/
def differential (s t : ℕ) : cochains s t →ₗ[F2] cochains (s + 1) t :=
  ((differentialPolynomial s).comp (cochains s t).subtype).codRestrict _
    (differentialPolynomial_mem s t)

/-- The cochain product used to define the square. -/
def cup {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    cochains (s + s') (t + t') :=
  ⟨cupPolynomial x.val y.val, cupPolynomial_mem x y⟩

end

end KIP126.Steenrod.Milnor
