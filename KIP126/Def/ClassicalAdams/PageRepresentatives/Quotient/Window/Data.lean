module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- In the nonzero window the model is the actual permanent-cycle quotient. -/
def nuEInftyWindow (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2) :
    nuEInftyModel H X p w ≃ₗ[ℤ] PermanentQuotient H X (1 + p.2 - w) p := by
  unfold nuEInftyModel
  rw [if_pos hw]
  exact LinearEquiv.refl ℤ _

/-- In its nonzero window the finite model is the actual Z/B subquotient. -/
def finiteEInftyWindow (q : ℕ) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q) :
    finiteEInftyModel H X q p w ≃ₗ[ℤ]
      CycleQuotient H X (q - p.2 + w) (1 + p.2 - w) p := by
  unfold finiteEInftyModel
  rw [if_pos hw]
  exact LinearEquiv.refl ℤ _

end
end KIP126.Classical.Adams.PageRepresentatives
