module

import all KIP126.Main.RepresentativeResults
import all KIP126.Main.SectionSeven.Final
/-! The universal representative form of the Table 1 contradiction.
The representative is obtained from the permanent U class and its actual
lift; the contradiction is the proved Section 7 argument. -/

@[expose] section
namespace KIP126.Main

/-- The actual-system version of the former Table 1 axiom. -/
private theorem table1 (hc3 : Stem126D6Vanishes) (h : ∀ u, UChoice u → EtaExtensionDetectionAt u) : False := by
  obtain ⟨u, hu⟩ := u_choice_exists
  exact SectionSeven.eta_extension_excluded_of_d6_vanishes hc3 ⟨u, hu, h u hu⟩

end KIP126.Main
