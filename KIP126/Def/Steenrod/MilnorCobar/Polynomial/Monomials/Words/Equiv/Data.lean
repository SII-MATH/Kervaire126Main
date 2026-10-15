module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Proofs
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra
open scoped TensorProduct DirectSum

/-- One nonconstant monomial of the specified integer degree. -/
abbrev PositiveMonomial (t : ℤ) :=
  {d : ℕ →₀ ℕ // (slotWeight d : ℤ) = t ∧ d ≠ 0}

/-- Separate a word into its first factor and remaining factors, retaining
the first factor's degree as the direct-sum index. -/
def wordConsEquiv (s : ℕ) (t : ℤ) :
    (Σ i : ℤ, PositiveMonomial i × MilnorWord s (t - i)) ≃ MilnorWord (s + 1) t where
  toFun x := ⟨Fin.cons x.2.1.val x.2.2.val, by
    constructor
    · rw [wordDegree_cons, x.2.1.property.1, x.2.2.property.1]
      omega
    · intro i
      exact Fin.cases x.2.1.property.2 x.2.2.property.2 i⟩
  invFun x := ⟨slotWeight (x.val 0),
    ⟨x.val 0, rfl, x.property.2 0⟩,
    ⟨fun i => x.val i.succ, by
      constructor
      · have h := x.property.1
        rw [wordDegree, Fin.sum_univ_succ] at h
        change wordDegree (fun i => x.val i.succ) = _
        dsimp only [wordDegree]
        omega
      · intro i
        exact x.property.2 i.succ⟩⟩
  left_inv x := by
    rcases x with ⟨i, ⟨a, ha, hne⟩, ⟨d, hd⟩⟩
    subst i
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The polynomial monomial basis is precisely the basis of nonempty-slot words. -/
def cochainMonomialEquivWord (s t : ℕ) : CochainMonomial s t ≃ MilnorWord s t :=
  (slotExponentsEquiv s).subtypeEquiv fun d => by
    simp only [IsCochainMonomial, wordDegree_slotExponents, Int.natCast_inj,
      usesSlot_iff_exponents_ne_zero]

/-- Word coefficients for the original normalized polynomial cochains. -/
def cochainsWordEquiv (s t : ℕ) :
    cochains s t ≃ₗ[F2] (MilnorWord s t →₀ F2) :=
  (cochainsMonomialEquiv s t).trans
    (Finsupp.domLCongr (cochainMonomialEquivWord s t))

/-- Tensoring a positive monomial factor with the remaining words and summing
over its integer degree gives all words of one greater length. -/
def wordTensorEquiv (s : ℕ) (t : ℤ) :
    (⨁ i : ℤ, (PositiveMonomial i →₀ F2) ⊗[F2] (MilnorWord s (t - i) →₀ F2)) ≃ₗ[F2]
      (MilnorWord (s + 1) t →₀ F2) :=
  (DirectSum.congrLinearEquiv fun i =>
    finsuppTensorFinsuppLid F2 F2 (PositiveMonomial i) (MilnorWord s (t - i))).trans
      ((sigmaFinsuppLequivDFinsupp F2).symm.trans (Finsupp.domLCongr (wordConsEquiv s t)))

end

end KIP126.Steenrod.Milnor
