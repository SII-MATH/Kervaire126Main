module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Proofs
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra
open scoped Classical

/-- One normalized tensor monomial of the specified internal degree. -/
abbrev CochainMonomial (s t : ℕ) :=
  {d : (Fin s × ℕ) →₀ ℕ // IsCochainMonomial t d}

/-- The existing polynomial cochains, with their actual monomial coefficients.
No dimension count or chosen vector-space basis is used. -/
def cochainsMonomialEquiv (s t : ℕ) :
    cochains s t ≃ₗ[F2] (CochainMonomial s t →₀ F2) :=
  ((AddMonoidAlgebra.coeffLinearEquiv F2).ofSubmodules _ _ (cochains_map_coeff s t)).trans
    (Finsupp.supportedEquivFinsupp {d | IsCochainMonomial t d})

/-- The canonical monomial basis of normalized homogeneous cobar cochains. -/
def cochainsMonomialBasis (s t : ℕ) : Module.Basis (CochainMonomial s t) F2 (cochains s t) where
  repr := cochainsMonomialEquiv s t

end

end KIP126.Steenrod.Milnor
