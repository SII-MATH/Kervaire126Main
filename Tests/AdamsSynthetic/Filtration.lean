module

import KIP126.Def.AdamsSynthetic

/-! Fixed filtration theorems keep their actual finiteness and torsion premises. -/
open CategoryTheory KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard
noncomputable section

example {X Y : Spectrum} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ∀ s : ℤ, FactorizationFiltration coefficients f s) :
    IsOddTorsionMap f := Standard.separated_factorization hX hY f hf

example {X Y : Spectrum} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s :=
  Standard.finite_filtration_of_not_odd hX hY f hf

example (X : Spectrum) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → ∀ x : HomotopyGroup i X,
      x ≠ 0 → x ∉ (classicalTower.tower X).filtrationSubmodule s i :=
  filtration_excludes_nonzero X hX hr hl i

example (T : HoCofiberSequence (C := Spectrum)) (i : ℤ) (nX nY : ℕ)
    (hX : ∀ S : Finset (ModTwoHomology coefficients (i-1) T.X), S.card ≤ nX)
    (hY : ∀ S : Finset (ModTwoHomology coefficients i T.Y), S.card ≤ nY)
    (S : Finset (ModTwoHomology coefficients i T.Z)) : S.card ≤ nX*nY :=
  cofiber_homology_card_bound T i nX nY hX hY S

example {X Y : Spectrum} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s ∧
      Nonempty (NonzeroClassicalDetection (mappingConvergence X Y hX hY) (s,s)
        (mappingClass closedBackground f s)) :=
  mapping_detect_non_odd hX hY f hf

-- Nonzeroness cannot replace the genuine non-odd-torsion premise.
example {X Y : Spectrum} (f : X ⟶ Y) (_hf : f ≠ 0) : True := by
  fail_if_success have : ¬ IsOddTorsionMap f := _hf
  trivial
end
