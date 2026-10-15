module

public import KIP126.Main.SectionSeven.PropositionSevenNine

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison
local notation "M" => standardMilnorCooperations
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0



-- The paper statement records the particular α₁ and its properties even
-- though the contradiction below is independent of that choice.
set_option linter.unusedVariables false in
/-- Lemma 7.16 (`lem:toda2ext`): the Toda bracket is nonempty and each member
is detected by λ⁴h₀²x₁₂₅,₉,₂. Here Proposition 7.9 is proved first by the
weak-representative argument; its contradiction yields this conditional
statement. This lemma is not used in that proof of Proposition 7.9. -/
theorem lemma_7_16_toda_bracket_detected
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M (D).toAdamsComparisonData L η)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 11))
    (ha : AlphaOneProperties D η h₀ ((L).U M) eV a11) :
    let a9 := a11 ≫ ((D).quotientTower S_0_0).rho 9 11 (by decide)
    (∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z) ∧
    (∀ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z →
      FiniteDetected D 9 (by decide) 11 136 4 eY z) := by
  exact False.elim (proposition_7_9 hc3 hc5)

end
end KIP126.Main.SectionSeven
