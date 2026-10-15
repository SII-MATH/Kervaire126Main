module

public import KIP126.Literature.Standard.ClassicalContext

@[expose] public section

/-! The type of a synthetic Adams context over the fixed classical H𝔽₂
category and Milnor coordinates. A particular context is assumed separately
in `KIP126.Literature.Background.SyntheticAdams`. -/
namespace KIP126.Classical.Adams
/-- The type of a synthetic Adams context over the fixed classical H𝔽₂ category. -/
noncomputable abbrev StandardSyntheticContext :=
  KIP126.Foundation.SyntheticAdamsContext KIP126.Def.standardHF2AdamsContext.stableContext
    KIP126.Def.standardHF2AdamsContext.milnorCoordinates

end KIP126.Classical.Adams
