module

public import KIP126.Def.AdamsSynthetic

/-! Parameterized consumers of the five filtration/homology obligations.
The finite and non-odd-torsion hypotheses, same tower, and actual mapping
spectrum remain visible at the point of use. -/
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.AdamsSynthetic
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : ModTwoCoefficients C}
  {A : ClassicalAdamsFamily C} (P : ClassicalTowerPresentation H.unit A)

example (comparison : FactorizationFiltrationComparison P)
    (separation : FiniteMapSeparation P) {X Y : C}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, FactorizationFiltration H f s) : IsOddTorsionMap f :=
  separated_factorization P comparison separation hX hY f hf

example (comparison : FactorizationFiltrationComparison P)
    (separation : FiniteMapSeparation P) {X Y : C}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, FactorizationFiltration H f s ∧ ¬ FactorizationFiltration H f (s+1) := by
  obtain ⟨s, hs, hn⟩ := finite_filtration_of_not_odd P separation hX hY f hf
  exact ⟨s, (comparison.agrees f s).mpr hs,
    fun h => hn ((comparison.agrees f (s+1)).mp h)⟩

example (B : AdamsBoundednessInput P) (X : C) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → ∀ x : HomotopyGroup i X,
      x ≠ 0 → x ∉ (P.tower X).filtrationSubmodule s i :=
  B.excludes_nonzero X hX hr hl i

-- Boundedness never excludes the zero element.
example (X : C) (s i : ℤ) :
    (0 : HomotopyGroup i X) ∈ (P.tower X).filtrationSubmodule s i :=
  filtration_contains_zero P X s i

example (E : ModTwoHomologyExactness H) (T : HoCofiberSequence (C := C))
    (i : ℤ) (nX nY : ℕ)
    (hX : ∀ S : Finset (ModTwoHomology H (i-1) T.X), S.card ≤ nX)
    (hY : ∀ S : Finset (ModTwoHomology H i T.Y), S.card ≤ nY)
    (S : Finset (ModTwoHomology H i T.Z)) : S.card ≤ nX*nY :=
  E.cofiber_card_bound T i nX nY hX hY S

example (B : ClosedSymmetricTensorTriangulated C)
    (S : MappingSpectrumSystem B P (IsFiniteSpectrum (C := C)))
    (D : MappingDetectionInput B P S) (separation : FiniteMapSeparation P)
    {X Y : C} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration P f s ∧
      ∃ x : (A.obj (mappingSpectrum B X Y)).Page 2 (s,s),
        ClassicalDetects (S.convergence X Y hX hY) (s,s) x (mappingClass B f s) := by
  obtain ⟨s, hs, ⟨w⟩⟩ := D.detect_non_odd separation hX hY f hf
  exact ⟨s, hs, w.pageElement, w.detects⟩

-- A nonzero infinity representative cannot be borrowed from another
-- convergence comparison, even when the underlying tower is the same.
example {X : C} (c _d : ClassicalTowerConvergence P X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) X) (_w : NonzeroClassicalDetection c p a) : True := by
  fail_if_success have : NonzeroClassicalDetection _d p a := _w
  trivial

example (_Q : ClassicalTowerPresentation H.unit A)
    (_comparison : FactorizationFiltrationComparison P) : True := by
  fail_if_success have : FactorizationFiltrationComparison _Q := _comparison
  trivial

-- Nonzeroness alone does not provide the old overbroad non-odd-torsion premise.
example {X Y : C} (f : X ⟶ Y) (_hf : f ≠ 0) : True := by
  fail_if_success have : ¬ IsOddTorsionMap f := _hf
  trivial
end
