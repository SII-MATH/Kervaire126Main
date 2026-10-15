module

public import KIP126.Def.Steenrod.MilnorCobar.Hi.Data
public import KIP126.Def.Steenrod.MilnorCobar.Multiplication.Proofs

@[expose] public section

/-! Closedness and compatibility with the previously constructed `h₆` representatives. -/

namespace KIP126.Steenrod.Milnor

noncomputable section

theorem hiCochain_isCycle (i : ℕ) : IsCycle (hiCochain i) := by
  apply Subtype.ext
  exact hiPolynomial_differential i

theorem hiSquareCochain_isCycle (i : ℕ) : IsCycle (hiSquareCochain i) := by
  have transport (t t' : ℕ) (ht : t = t') (x : cochains 2 t) (hx : IsCycle x) :
      IsCycle (reindex rfl ht x) := by
    subst t'
    exact hx
  exact transport _ _ (hiSquare_internalDegree i) _
    (cup_isCycle _ _ (hiCochain_isCycle i) (hiCochain_isCycle i))

end

end KIP126.Steenrod.Milnor
