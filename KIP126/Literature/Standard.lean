module

public import KIP126.Literature.Standard.ClassicalContext

@[expose] public section

/-! The classical context underlying the standard Adams/synthetic comparison.
All sphere classes, synthetic objects and external results use the same
HF₂-local category and the same Milnor coordinates. -/
namespace KIP126.AdamsSynthetic.Standard

/-- The classical HF₂ Adams context fixed by `Def.standardHF2AdamsContext`. -/
noncomputable def classicalContext : KIP126.HF2AdamsContext KIP126.StableHomotopy.Spectra.completionModel := KIP126.Def.standardHF2AdamsContext

end KIP126.AdamsSynthetic.Standard
