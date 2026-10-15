module

public import KIP126.Def.AdamsSynthetic.Conditions.D12Criterion
public import KIP126.Def.AdamsSynthetic.Conditions.EtaExtension
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

namespace KIP126.Main
/-- The logical deduction of LWX Theorem 7.1 from Propositions 7.8 and 7.9.
Both propositions are hypotheses here; `h6_sq_permanent` applies this
implication to their proofs for the standard sphere. -/
theorem h6_square_permanent_of_differential_criterion_and_eta_obstruction (η : BiHom 1 2 (S_0_0 : Syn))
    (hη : EtaChoice M D.toAdamsComparisonData η)
    (hcriterion : KIP126.Main.Stem126.OnlyD12.d12_dichotomy_and_condition_equivalence M D L η)
    (hobstruction : KIP126.Main.Stem126.EtaExtensionObstruction.eta_extension_excluded_of_d6_vanishes M D L η) :
    PermanentH6Square M := by
  obtain ⟨cases, criteria⟩ := hcriterion hη
  rcases cases with h | h
  · exact h.1
  · obtain ⟨hvanishing, _, hextension⟩ := criteria.mp h.1
    exact False.elim (hobstruction hη hvanishing hextension)
end KIP126.Main
