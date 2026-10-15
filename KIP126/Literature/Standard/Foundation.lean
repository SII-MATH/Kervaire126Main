module

public import KIP126.Literature.Standard

@[expose] public section

/-! Compatibility name for the foundation fixed in Def. -/
namespace KIP126.Classical.Adams

noncomputable def standardFoundation : StandardAdamsFoundation :=
  KIP126.AdamsSynthetic.Standard.classicalContext.foundation

end KIP126.Classical.Adams
