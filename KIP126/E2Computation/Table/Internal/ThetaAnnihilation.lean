module
import all KIP126.E2Computation.Standard
import all KIP126.E2Computation.Internal.ThetaCertificate

/-! Connect the fixed native-quotient h₅ certificate to the existing source
component. The actual E₂ comparison remains in Table.ThetaRelations. -/

namespace KIP126.Computation.Table.Internal
open KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem thetaSourceZero (x : sourceData.component 7 70) :
    sourceData.product 1 32 7 70 (sourceData.atom .h5) x = 0 := by
  apply Subtype.ext
  change nativeProjection generators.count archiveSourceRelations
    (MvPolynomial.X ⟨18, by decide⟩) * x.val = 0
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  have h := thetaRawZero
    (nativePartToCached generators.count generators.degree archiveSourceRelations 7 70 x)
  change CachedStandard.nativeProjection generators.count archiveSourceRelations
    (MvPolynomial.X ⟨18, by decide⟩) *
      nativeEquiv generators.count archiveSourceRelations x.val = 0 at h
  simpa only [map_mul, nativeEquiv_projection, map_zero] using h

end
end KIP126.Computation.Table.Internal
