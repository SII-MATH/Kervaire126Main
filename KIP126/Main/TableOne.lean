module

public import KIP126.Main.RepresentativeResults
public import KIP126.Main.SectionSeven.Final

/-! The universal representative form of the Table 1 contradiction.
The representative is obtained from the permanent U class and its actual
lift; the contradiction is the proved Section 7 argument. -/

@[expose] section
namespace KIP126.Main

/-- The actual-system version of the former Table 1 axiom. -/
public theorem table1 (hc3 : C3) (h : ∀ u, UChoice u → C5At u) : False := by
  obtain ⟨u, hu⟩ := u_choice_exists
  exact SectionSeven.c3_excludes_c5 hc3 ⟨u, hu, h u hu⟩

end KIP126.Main
