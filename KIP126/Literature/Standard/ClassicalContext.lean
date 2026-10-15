module

public import KIP126.Literature.Background.ClassicalAdams

@[expose] public section

/-! The fixed HF₂-local classical Adams context.
The choice below uses the explicitly assumed existence of an `HF2AdamsContext`.
Its category, H𝔽₂, Milnor coordinates and smash product are the ones used
throughout the classical and synthetic comparisons. -/
namespace KIP126.Def

/-- The standard classical Adams context selected from the background
existence assumption. This definition does not prove that assumption. -/
noncomputable def standardHF2AdamsContext : KIP126.HF2AdamsContext KIP126.StableHomotopy.Spectra.completionModel :=
  Classical.choice KIP126.AdamsSynthetic.hf2AdamsContext_exists

end KIP126.Def
