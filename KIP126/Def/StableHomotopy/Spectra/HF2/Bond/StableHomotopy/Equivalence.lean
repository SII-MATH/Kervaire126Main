module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.StableHomotopy

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The actual stable-degree-zero equivalence obtained from the fixed
structure maps and specified normalized degree-zero coefficients. -/
noncomputable def coefficientStableZeroEquiv :
    Prespectrum.StableHomotopy hf2RealizationPrespectrum 0 ≃ ZMod 2 :=
  Equiv.ofBijective (coefficientStableCode hb) (coefficientStableCode_bijective hb)

end KIP126.StableHomotopy.Spectra.HF2Bond

end

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The stable equivalence agrees with the displayed level calculation. -/
@[simp] theorem coefficientStableZeroEquiv_class (n : ℕ)
    (hr : (n : ℤ) = 0 + n)
    (p : GenLoop (Fin n) (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    coefficientStableZeroEquiv hb
      (Prespectrum.loopClass hf2RealizationPrespectrum 0 n n hr p) =
        coefficientDiagonalEquiv hb n ⟦p⟧ := rfl

/-- The stable equivalence sends the actual constant representative to zero. -/
@[simp] theorem coefficientStableZeroEquiv_zero :
    coefficientStableZeroEquiv hb
      (Prespectrum.loopClass hf2RealizationPrespectrum 0 0 0 (by simp) GenLoop.const) = 0 := by
  rw [coefficientStableZeroEquiv_class,coefficientDiagonalEquiv_const]

/-- The stable equivalence preserves the actual cubical concatenation
specified in the source Eilenberg–Mac Lane characterization. -/
theorem coefficientStableZeroEquiv_add (n : ℕ)
    (p q : GenLoop (Fin (n+1)) (hf2RealizationLevel (n+1)) (hf2RealizationLevel (n+1)).point) :
    coefficientStableZeroEquiv hb
      (Prespectrum.loopClass hf2RealizationPrespectrum 0 (n+1) (n+1) (by omega)
        (GenLoop.transAt 0 p q)) =
      coefficientStableZeroEquiv hb
        (Prespectrum.loopClass hf2RealizationPrespectrum 0 (n+1) (n+1) (by omega) p) +
      coefficientStableZeroEquiv hb
        (Prespectrum.loopClass hf2RealizationPrespectrum 0 (n+1) (n+1) (by omega) q) := by
  simpa only [coefficientStableZeroEquiv_class] using coefficientDiagonalEquiv_transAt hb n p q

end KIP126.StableHomotopy.Spectra.HF2Bond

end
