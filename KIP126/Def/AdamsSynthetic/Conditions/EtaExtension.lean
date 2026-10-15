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

namespace KIP126.Main.Stem126.EtaExtensionObstruction
/-- The proposition expressing LWX Proposition 7.9 on a given sphere model.
The d₆ differential, η, product and detection all use that same model.
`KIP126.Main.SectionSeven.proposition_7_9` proves its standard-sphere case. -/
def eta_extension_excluded_of_d6_vanishes (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η → Stem126D6Vanishes L → ¬ EtaExtensionDetection M D.toAdamsComparisonData L η
end KIP126.Main.Stem126.EtaExtensionObstruction


