module

public import KIP126.Main.Computation.LinCoordinates.PresentationTheorems

public import KIP126.Main.AdamsSynthetic.Context

@[expose] public section

/-! The E₂ presentation identifying the computation coordinates with the
standard sphere, taken from the common external hypotheses. -/
namespace KIP126.Classical.Adams

noncomputable def linE2Presentation : LinE2Presentation :=
  KIP126.Main.AdamsSynthetic.computation.interpretation.presentation

end KIP126.Classical.Adams
