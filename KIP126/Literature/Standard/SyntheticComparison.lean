module

public import KIP126.Literature.Background.SyntheticAdams

@[expose] public section

/-! The fixed synthetic Adams context assumed in
`KIP126.Literature.Background.SyntheticAdams`.
These definitions refer to that same assumed context and its classical/synthetic
comparison. They do not give a construction or a proof of its existence. -/
namespace KIP126.Def

/-- The synthetic category and Adams comparisons used by the literature,
computation and main argument, over the fixed classical H𝔽₂ context. -/
noncomputable abbrev standardSyntheticContext := KIP126.AdamsSynthetic.standardSyntheticContext

end KIP126.Def

namespace KIP126.Classical.Adams

/-- The classical/synthetic Adams comparison in the fixed synthetic context. -/
noncomputable abbrev standardAdamsComparison := KIP126.Def.standardSyntheticContext.adamsComparison

end KIP126.Classical.Adams
