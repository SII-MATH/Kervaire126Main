module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Homotopy.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The coefficient map on the actual stable quotient, descended through
the proved homotopy and stabilization relations. -/
noncomputable def coefficientStableCode :
    Prespectrum.StableHomotopy hf2RealizationPrespectrum 0 → ZMod 2 :=
  Quot.lift (coefficientDiagonalRepresentative hb) fun _ _ h =>
    coefficientDiagonalRepresentative_relation hb h

end KIP126.StableHomotopy.Spectra.HF2Bond

end

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The stable coefficient of a displayed level class is its diagonal coefficient. -/
@[simp] theorem coefficientStableCode_class (n : ℕ)
    (x : HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    coefficientStableCode hb (coefficientDiagonalClass n x) = coefficientDiagonalEquiv hb n x := by
  induction x using Quotient.inductionOn with
  | h p => rfl

theorem coefficientStableCode_normalForm
    (x : Prespectrum.StableHomotopy hf2RealizationPrespectrum 0) :
    x = coefficientDiagonalClass 0 (coefficientZeroPiZeroEquiv.symm (coefficientStableCode hb x)) := by
  induction x using Quot.inductionOn with
  | h a =>
    obtain ⟨n,r,hr,p⟩ := a
    have heq : r = n := by omega
    subst r
    exact coefficientDiagonalClass_normalForm hb n ⟦p⟧

/-- The actual stable coefficient map is bijective, with its inverse
represented at degree zero. -/
theorem coefficientStableCode_bijective : Function.Bijective (coefficientStableCode hb) := by
  constructor
  · intro x y h
    rw [coefficientStableCode_normalForm hb x,coefficientStableCode_normalForm hb y,h]
  · intro a
    refine ⟨coefficientDiagonalClass 0 (coefficientZeroPiZeroEquiv.symm a),?_⟩
    rw [coefficientStableCode_class]
    exact coefficientZeroPiZeroEquiv.apply_symm_apply a

end KIP126.StableHomotopy.Spectra.HF2Bond

end
