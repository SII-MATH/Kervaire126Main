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

/-- Corollary 7.18 (`cor:2ext125`): every λ⁴h₀²x₁₂₅,₉,₂ representative
admits the stated h₀-extension, with a target representative depending on it.
The proof uses the contradiction of Proposition 7.9 under conditions (3)
and (5); it does not supply an unconditional d₅ computation. -/
theorem corollary_7_18_h0_extension
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M (D).toAdamsComparisonData L η) :
    AnyYH0Extension D eY ((L).target M) h₀ := by
  exact False.elim (proposition_7_9 hc3 hc5)


end
end KIP126.Main.SectionSeven
