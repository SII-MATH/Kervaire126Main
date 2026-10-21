module

import KIP126.ProofTools.MahowaldLeibniz
import all KIP126.ProofTools.MahowaldLeibniz.PositiveFirstCore
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGCore
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHCore

/-! Exhaustive normalization cases for the common finite-quotient core.
The three cases retain the same original triangle. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Literature

private theorem normalized_exponent_cases
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    (normalizedExponent model.classicalTower T.f = 1 ∧
      normalizedExponent model.classicalTower T.g = 0 ∧
      normalizedExponent model.classicalTower T.h = 0) ∨
    (normalizedExponent model.classicalTower T.f = 0 ∧
      normalizedExponent model.classicalTower T.g = 1 ∧
      normalizedExponent model.classicalTower T.h = 0) ∨
    (normalizedExponent model.classicalTower T.f = 0 ∧
      normalizedExponent model.classicalTower T.g = 0 ∧
      normalizedExponent model.classicalTower T.h = 1) := by
  omega

/-- The complete finite-quotient core, expressed in the three exhaustive
normalization coordinates of the same triangle. Each component constructs
its May representative from classical inputs, preserves its exact signed
target, proves the original source's cycle qualification, and compares all
representatives with that label under independent ambiguity annihilation.
All finite levels and compatible comparison choices are quantified inside
the three component statements. -/
private def FiniteQuotientMahowaldLeibnizCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) : Prop :=
  (∀ hf hg hh, PositiveFirstFiniteCoreStatement T he hT hf hg hh) ∧
  (∀ hf hg hh, PositiveSecondFiniteCoreStatement T he hT hf hg hh) ∧
  (∀ hf hg hh, PositiveThirdFiniteCoreStatement T he hT hf hg hh)

/-- The common core has no chosen-producer or output-survival premise.
The cases in `normalized_exponent_cases` show that its three statements
cover every compatible normalized triangle admitted by the exponent sum. -/
private theorem finite_quotient_mahowald_leibniz_core
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    FiniteQuotientMahowaldLeibnizCoreStatement T he hT :=
  ⟨fun hf hg hh => positive_first_finite_core T he hT hf hg hh,
    fun hf hg hh => positive_second_finite_core T he hT hf hg hh,
    fun hf hg hh => positive_third_finite_core T he hT hf hg hh⟩

end KIP126.ProofTools.Internal.MahowaldLeibniz
