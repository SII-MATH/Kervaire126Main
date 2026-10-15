module

public import KIP126.Literature.Standard.Sphere.Algebra.Components
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Data

@[expose] public section

namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable abbrev actualE2GradedNonUnitalNonAssocSemiring :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2GradedNonUnitalNonAssocSemiring KIP126.Def.standardHF2AdamsContext

noncomputable abbrev ActualE2Total :=
  KIP126.Classical.Adams.Sphere.Algebra.ActualE2Total KIP126.Def.standardHF2AdamsContext

noncomputable abbrev embed :=
  KIP126.Classical.Adams.Sphere.Algebra.embed KIP126.Def.standardHF2AdamsContext

attribute [instance] actualE2GradedNonUnitalNonAssocSemiring

end KIP126.Classical.Adams.Sphere.Internal
