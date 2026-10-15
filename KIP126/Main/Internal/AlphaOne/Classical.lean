module
import all KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Def.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.ThetaFrames

/-! The original classical E∞ deductions in AlphaOne.lean:171–223,
bbac1fc05843 (MIT), on the actual fixed sphere sequence. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal.Selected
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem classical_stem124_einfty_below_ten (s : ℤ) (hs : s<10) :
    Subsingleton ((model.classical.sphere.ssData (s,s+124)).eInfty) :=
  Selected.classical_low_infinity_zero s hs

private theorem classical_stem124_af10_generated :
    KIP126.Main.SectionSeven.ClassicalInfinityGenerated 10 134 KIP126.Computation.Standard.U :=
  Selected.u_infinity_generated

private theorem classical_stem124_af13_generated :
    KIP126.Main.SectionSeven.ClassicalInfinityGenerated 13 137 KIP126.Computation.Standard.correction :=
  Selected.correction_infinity_generated

end
end KIP126.Main.Internal.AlphaOne
end
