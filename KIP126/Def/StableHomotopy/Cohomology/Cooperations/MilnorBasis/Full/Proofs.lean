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

theorem cooperationReducedEquivOfNe_val (n : ℤ) (hn : n ≠ 0)
    (a : Mod2Cooperations H n) : (cooperationReducedEquivOfNe H R n hn a).val = a := rfl

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

/-- Nonzero-degree coordinates are the given reduced basis coordinates,
not a newly chosen basis of the full cooperation group. -/
theorem cooperationMilnorEquiv_of_ne (n : ℤ) (hn : n ≠ 0)
    (a : Mod2Cooperations H n) (d : MilnorMonomial n) :
    cooperationMilnorEquiv H R B n a d =
      (B.basis n).repr (cooperationReducedEquivOfNe H R n hn a)
        (milnorMonomialEquivPositive n hn d) := by
  simp [cooperationMilnorEquiv, hn, Finsupp.domLCongr_apply]

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

/-- Linear identities on genuine cooperations reduce to the actual unit
and the supplied reduced basis. No multiplication or coproduct is assumed. -/
theorem cooperation_linearMap_ext {W : ℤ → Type w}
    [∀ n, AddCommGroup (W n)] [∀ n, Module (ZMod 2) (W n)]
    (f g : ∀ n, mod2HomologyF2 H R n H.HF2 →ₗ[ZMod 2] W n)
    (hunit : f 0 (cooperationUnit H) = g 0 (cooperationUnit H))
    (hb : ∀ n (d : PositiveMonomial n),
      f n ((B.basis n) d).val = g n ((B.basis n) d).val) : f = g := by
  funext n
  let e := cooperationMilnorEquiv H R B n
  have he : (f n).comp e.symm.toLinearMap = (g n).comp e.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro d c
    have hc : Finsupp.single d c = c • Finsupp.single d (1 : ZMod 2) := by simp
    rw [hc, map_smul, map_smul]
    congr 1
    change f n (e.symm (Finsupp.single d 1)) = g n (e.symm (Finsupp.single d 1))
    by_cases hn : n = 0
    · subst n
      have h : e.symm (Finsupp.single d 1) = cooperationUnit H := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (milnorMonomial_zero_eq d) ▸ (cooperationMilnorEquiv_unit H R B).symm
      rw [h]
      exact hunit
    · let d' : PositiveMonomial n := ⟨d.val, d.property, milnorMonomial_ne_zero hn d⟩
      have h : e.symm (Finsupp.single d 1) = ((B.basis n) d').val := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (cooperationMilnorEquiv_reduced_basis H R B n d').symm
      rw [h]
      exact hb n d'
  apply LinearMap.ext
  intro a
  have h := LinearMap.congr_fun he (e a)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply] using h

end

end KIP126.StableHomotopy.Cohomology
