module

public import KIP126.Def.Steenrod.MilnorCobar.Data

@[expose] public section

/-! # Transport along equal cobar bidegrees -/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- The canonical linear equivalence between equal cochain bidegrees. -/
def reindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t') :
    cochains s t ≃ₗ[KIP126.Algebra.F2] cochains s' t' := by
  subst s'
  subst t'
  exact LinearEquiv.refl _ _

end

end KIP126.Steenrod.Milnor
