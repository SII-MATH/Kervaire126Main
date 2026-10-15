module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

/-- The unique empty word in degree zero. -/
def emptyMilnorWord : MilnorWord 0 0 :=
  ⟨Fin.elim0, by simp [wordDegree], fun i => Fin.elim0 i⟩

/-- The single cooperation monomial ξ₁^64. -/
noncomputable def h6PositiveMonomial : PositiveMonomial 64 :=
  ⟨Finsupp.single 0 64, by simp [slotWeight, Finsupp.weight_single], by simp⟩

/-- The length-one word [ξ₁^64]. -/
noncomputable def h6MilnorWord : MilnorWord 1 64 :=
  wordConsEquiv 0 64 ⟨64, h6PositiveMonomial, emptyMilnorWord⟩

/-- The length-two word [ξ₁^64 | ξ₁^64]. -/
noncomputable def h6SquareMilnorWord : MilnorWord 2 128 :=
  wordConsEquiv 1 128 ⟨64, h6PositiveMonomial, h6MilnorWord⟩

end KIP126.Steenrod.Milnor
