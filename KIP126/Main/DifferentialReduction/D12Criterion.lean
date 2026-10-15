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

namespace KIP126.Main.Stem126.OnlyD12
/-- The proposition expressing LWX Proposition 7.8 on a given sphere model.
This definition states the exclusive permanence/d₁₂ dichotomy and the
criterion for d₁₂. `KIP126.Main.proposition_7_8` proves it for the standard
model from the external literature and computation hypotheses. -/
def d12_dichotomy_and_condition_equivalence (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η →
    (((PermanentH6Square M ∧ ¬ H6SquareSupportsD12 M L) ∨
        (H6SquareSupportsD12 M L ∧ ¬ PermanentH6Square M)) ∧
      (H6SquareSupportsD12 M L ↔ Stem126D6Vanishes L ∧ Theta5SquareNonzeroDetection M D.toAdamsComparisonData L ∧ EtaExtensionDetection M D.toAdamsComparisonData L η))
end KIP126.Main.Stem126.OnlyD12
