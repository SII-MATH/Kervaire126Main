module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Homotopy.Data
public import KIP126.Def.Algebra.Group.TwoElements.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The diagonal calculation strictly respects the specified structure map. -/
@[simp] theorem coefficientDiagonalEquiv_bond (n : ℕ)
    (x : HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    coefficientDiagonalEquiv hb (n+1) (bondHomotopyMap n n x) =
      coefficientDiagonalEquiv hb n x := by
  change coefficientDiagonalEquiv hb n
    ((Equiv.ofBijective (bondHomotopyMap n n) (hb n n)).symm
      ((Equiv.ofBijective (bondHomotopyMap n n) (hb n n)) x)) = _
  rw [Equiv.symm_apply_apply]

/-- The actual structure map preserves the constant cubical class. -/
@[simp] theorem bondHomotopyMap_const (n r : ℕ) :
    bondHomotopyMap n r ⟦GenLoop.const⟧ = ⟦GenLoop.const⟧ := by
  rw [bondHomotopyMap_mk,Prespectrum.stabilizeLoop_const]

/-- The specified degree-zero coefficient equivalence preserves zero. -/
@[simp] theorem coefficientZeroPiZeroEquiv_const :
    coefficientZeroPiZeroEquiv ⟦GenLoop.const⟧ = 0 := by
  change coefficientZeroRealizationHomeomorph (hf2RealizationLevel 0).point = (0 : ZMod 2)
  exact coefficientZeroRealizationHomeomorph_point

/-- Every diagonal coefficient calculation sends the actual constant class to zero. -/
@[simp] theorem coefficientDiagonalEquiv_const (n : ℕ) :
    coefficientDiagonalEquiv hb n ⟦GenLoop.const⟧ = 0 := by
  induction n with
  | zero => exact coefficientZeroPiZeroEquiv_const
  | succ n ih =>
    rw [← bondHomotopyMap_const n n,coefficientDiagonalEquiv_bond,ih]

include hb in
/-- Off-diagonal genuine cubical homotopy sets vanish once the actual
structure maps are bijective on cubical homotopy. -/
theorem coefficientPi_subsingleton_of_ne (n r : ℕ) (hne : r ≠ n) :
    Subsingleton (HomotopyGroup.Pi r (hf2RealizationLevel n) (hf2RealizationLevel n).point) := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => exact False.elim (hne rfl)
    | succ r => exact coefficientZeroPiPositive_subsingleton r
  | succ n ih =>
    cases r with
    | zero => exact coefficientPositivePiZero_subsingleton n
    | succ r =>
      letI := ih r (by omega)
      exact (hb n r).surjective.subsingleton

include hb in
/-- The actual stable homotopy quotient vanishes in every nonzero integer
degree under the specified structure-map bijectivity. -/
theorem coefficientStableHomotopy_subsingleton_of_ne (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (Prespectrum.StableHomotopy hf2RealizationPrespectrum d) := by
  apply Prespectrum.stableHomotopy_subsingleton_of_eventually_level_homotopy_subsingleton 0
  intro n hn r hr
  exact coefficientPi_subsingleton_of_ne hb n r (by omega)

theorem coefficientDiagonalRepresentative_relation
    {a b : Prespectrum.Representative hf2RealizationPrespectrum 0}
    (h : Prespectrum.StableRelation hf2RealizationPrespectrum 0 a b) :
    coefficientDiagonalRepresentative hb a = coefficientDiagonalRepresentative hb b := by
  cases h with
  | homotopy q h =>
    obtain ⟨n,r,hr,p⟩ := a
    have heq : r = n := by omega
    subst r
    exact congrArg (coefficientDiagonalEquiv hb n) (Quotient.sound h)
  | stabilization =>
    obtain ⟨n,r,hr,p⟩ := a
    have heq : r = n := by omega
    subst r
    exact (coefficientDiagonalEquiv_bond hb n ⟦p⟧).symm

/-- Stabilization does not change the actual stable class. -/
theorem coefficientDiagonalClass_bond (n : ℕ)
    (x : HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    coefficientDiagonalClass (n+1) (bondHomotopyMap n n x) = coefficientDiagonalClass n x := by
  induction x using Quotient.inductionOn with
  | h p => exact (Quot.sound (Prespectrum.StableRelation.stabilization
      (⟨n,n,by omega,p⟩ : Prespectrum.Representative hf2RealizationPrespectrum 0))).symm

/-- Every diagonal class has a degree-zero representative with exactly
the calculated coefficient. -/
theorem coefficientDiagonalClass_normalForm (n : ℕ)
    (x : HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    coefficientDiagonalClass n x = coefficientDiagonalClass 0
      (coefficientZeroPiZeroEquiv.symm (coefficientDiagonalEquiv hb n x)) := by
  induction n with
  | zero => rw [coefficientDiagonalEquiv,Equiv.symm_apply_apply]
  | succ n ih =>
    obtain ⟨y,rfl⟩ := (hb n n).surjective x
    rw [coefficientDiagonalClass_bond,coefficientDiagonalEquiv_bond]
    exact ih y

/-- The diagonal coefficient map preserves actual concatenation along
the first cube coordinate. The two-element group calculation handles the
standard homotopy-group multiplication convention. -/
theorem coefficientDiagonalEquiv_transAt (n : ℕ)
    (p q : GenLoop (Fin (n+1)) (hf2RealizationLevel (n+1)) (hf2RealizationLevel (n+1)).point) :
    coefficientDiagonalEquiv hb (n+1) ⟦GenLoop.transAt 0 p q⟧ =
      coefficientDiagonalEquiv hb (n+1) ⟦p⟧ + coefficientDiagonalEquiv hb (n+1) ⟦q⟧ := by
  rw [← HomotopyGroup.mul_spec]
  rw [KIP126.Algebra.equivTwo_map_mul (coefficientDiagonalEquiv hb (n+1))
    (coefficientDiagonalEquiv_const hb (n+1)),add_comm]

end KIP126.StableHomotopy.Spectra.HF2Bond
