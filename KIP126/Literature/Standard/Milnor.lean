module

public import KIP126.Literature.Standard.Foundation

@[expose] public section

/-! The Milnor coordinates on the fixed classical H𝔽₂ Adams context. -/
namespace KIP126.Classical.Adams

noncomputable def standardMilnorCooperations :
    MilnorCooperations standardFoundation.hf2 :=
  KIP126.AdamsSynthetic.Standard.classicalContext.milnor

end KIP126.Classical.Adams
