module

public import KIP126.Def.AdamsSynthetic.Conditions.Predicates
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data

@[expose] public section

open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : AdamsComparison H M Syn) (L : SphereAdamsClasses H)

namespace KIP126.Main.Stem126.Conditions
/-- The proposition expressing LWX Lemmas 7.10 and 7.11, without a proof:
condition (4) varies θ₅ in π_(62,64), whereas condition (5) varies
[h₀²x₁₂₄,₈] in π_(124,134). Establishing the equivalences also requires
the existence of admissible representatives. -/
def square_and_eta_detection_choice_equivalence (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η →
    (Theta5SquareNonzeroDetection M D.toAdamsComparisonData L ↔
      ∀ θ, ThetaChoice M D.toAdamsComparisonData θ → Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ) ∧
    (EtaExtensionDetection M D.toAdamsComparisonData L η ↔
      ∀ u, UChoice M D.toAdamsComparisonData L u → EtaExtensionDetectionAt M D.toAdamsComparisonData L η u)
end KIP126.Main.Stem126.Conditions
