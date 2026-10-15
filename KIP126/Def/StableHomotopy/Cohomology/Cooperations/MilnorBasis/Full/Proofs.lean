module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- In degree zero the constructed coordinate is exactly the counit
followed by the specified `π₀H = F₂` coordinate. -/
theorem cooperationMilnorEquiv_zero_coefficient (a : Mod2Cooperations H 0) :
    cooperationMilnorEquiv H R B 0 a zeroMilnorMonomial =
      H.pi0Equiv (cooperationCounit H R 0 a) := by
  simp only [cooperationMilnorEquiv]
  change milnorZeroCoefficientsEquiv.symm (H.pi0Equiv (cooperationCounit H R 0 a))
    zeroMilnorMonomial = _
  simp [milnorZeroCoefficientsEquiv]

/-- The actual cooperation unit becomes the constant polynomial basis vector. -/
theorem cooperationMilnorEquiv_unit :
    cooperationMilnorEquiv H R B 0 (cooperationUnit H) =
      Finsupp.single zeroMilnorMonomial 1 := by
  ext d
  rw [milnorMonomial_zero_eq d, cooperationMilnorEquiv_zero_coefficient,
    cooperationCounit_unit, H.pi0Equiv.apply_symm_apply, Finsupp.single_eq_same]

/-- The completion keeps every original reduced basis vector as the
corresponding nonconstant monomial. -/
theorem cooperationMilnorEquiv_reduced_basis (n : ℤ) (d : PositiveMonomial n) :
    cooperationMilnorEquiv H R B n ((B.basis n) d).val =
      Finsupp.single (⟨d.val, d.property.1⟩ : MilnorMonomial n) 1 := by
  have hn : n ≠ 0 := ne_of_gt (positiveMonomial_degree_pos d)
  have he : cooperationReducedEquivOfNe H R n hn ((B.basis n) d).val =
      (B.basis n) d := by
    apply Subtype.ext
    rfl
  simp [cooperationMilnorEquiv, hn, he, Module.Basis.repr_self,
    milnorMonomialEquivPositive]

end

end KIP126.StableHomotopy.Cohomology
