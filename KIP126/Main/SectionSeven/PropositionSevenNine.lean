module

public import KIP126.Main.SectionSeven.NuDivisibility
public import KIP126.Main.SectionSeven.CofiberRigidity

@[expose] public section

/-! LWX Proposition 7.9 (`prop:state5false`).

The ν-divisibility argument produces an incoming differential in the
ν-cofiber. The computed incoming-page exclusion makes this impossible.
The sphere classes and the cofiber calculation use the same external
hypotheses. Lemma 7.16 and Corollary 7.18 are subsequently recovered from
this contradiction, so the formal dependency order differs from the paper.
-/
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

/-- Proposition 7.9: condition (3) excludes condition (5) of Proposition 7.8.
The proof combines ν-divisibility with the ν-cofiber incoming-page exclusion. -/
theorem proposition_7_9
    (hc3 : Stem126D6Vanishes L) : ¬ EtaExtensionDetection M (D).toAdamsComparisonData L η := by
  intro hc5
  obtain ⟨y, hy, r, hr, hr', hhit⟩ :=
    target_divisibility_forces_cnu_incoming (target_nu_divisible hc3 hc5)
  obtain ⟨y', hy', _, hnot⟩ := KIP126.Computation.SphereAndCofiber.cnu_target_through5 I
  have hyy : y = y' := Option.some.inj (hy.symm.trans hy')
  subst y'
  exact hnot.2.2 r hr hr' hhit

end
end KIP126.Main.SectionSeven
