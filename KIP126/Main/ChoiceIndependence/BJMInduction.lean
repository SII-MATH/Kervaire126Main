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

namespace KIP126.Main.Stem126.BJMInduction
open KIP126.Kervaire
/-- The proposition expressing Theorem 7.3 and the choice independence
discussed in Remarks 7.4–7.5. It asks for the normalized criterion for every
admissible θ₅. The literature supplies the BX criterion at its source choice;
this definition supplies no proof of normalization or choice independence. -/
def any_choice_criterion (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η →
    ∀ θ, ThetaChoice M D.toAdamsComparisonData θ →
      BJMNormalizedFiniteCriterion H M η θ ∧
      BJMUntruncatedCriterion H M η θ
end KIP126.Main.Stem126.BJMInduction
