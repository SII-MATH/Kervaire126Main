module

public import KIP126.Literature.Standard.Foundation
public import KIP126.Literature.Standard.Milnor
public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Components.Data

@[expose] public section

/-! The sphere E₂ algebra construction specialized to the single standard
HF₂ Adams context. Its generic construction and identities are in Def. -/
namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable abbrev ActualE2At :=
  KIP126.Classical.Adams.Sphere.Algebra.ActualE2At KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2AtAddCommGroup :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtAddCommGroup KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2AtIntModule :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtIntModule KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2ToCobarInt :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2ToCobarInt KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2AtModule :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtModule KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2AtScalarTower :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtScalarTower KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2AtIntSMulComm :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtIntSMulComm KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2ToCobar :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2ToCobar KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2Product :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2Product KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2Unit :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2Unit KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2GradedOne :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2GradedOne KIP126.Def.standardHF2AdamsContext

noncomputable abbrev actualE2GradedMul :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2GradedMul KIP126.Def.standardHF2AdamsContext

attribute [instance] actualE2AtAddCommGroup actualE2AtIntModule actualE2AtModule actualE2AtScalarTower actualE2AtIntSMulComm actualE2GradedOne actualE2GradedMul

end KIP126.Classical.Adams.Sphere.Internal
