module
import all KIP126.E2Computation.Standard
import all KIP126.E2Computation.Internal.H2Certificate
/-! Source-presentation bridge for the cached native quotient h₂ certificate.
The fixed coordinate-selected generators remain unchanged. -/
namespace KIP126.Computation.Table.Internal
open KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false

-- Capture each cached declaration before restoring the original user name below.
private def h2CachedX (i : Fin CachedStandard.archiveGeneratorCount) := h2X i
private theorem h2CachedX_projection (i : Fin CachedStandard.archiveGeneratorCount) :
    h2CachedX i = CachedStandard.nativeProjection CachedStandard.archiveGeneratorCount
      CachedStandard.archiveSourceRelations (MvPolynomial.X i) := rfl
private theorem h2CachedRelation2 :
    (h2CachedX ⟨1,by decide⟩)^3 +
      (h2CachedX ⟨0,by decide⟩)^2 * (h2CachedX ⟨2,by decide⟩) = 0 :=
  h2Relation2
private theorem h2CachedRelation859 :
    (h2CachedX ⟨1,by decide⟩)^2 * (h2CachedX ⟨79,by decide⟩) = 0 :=
  h2Relation859

private def h2X (i : Fin generators.count) := nativeProjection generators.count archiveSourceRelations (MvPolynomial.X i)

private theorem h2Relation2 : (h2X ⟨1,by decide⟩)^3 + (h2X ⟨0,by decide⟩)^2 * (h2X ⟨2,by decide⟩) = 0 := by
  have hm (i : Fin generators.count) :
      nativeEquiv generators.count archiveSourceRelations (h2X i) = h2CachedX i := by
    rfl
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  simpa only [map_add, map_mul, map_pow, map_zero, hm] using h2CachedRelation2

private theorem h2Relation859 : (h2X ⟨1,by decide⟩)^2 * (h2X ⟨79,by decide⟩) = 0 := by
  have hm (i : Fin generators.count) :
      nativeEquiv generators.count archiveSourceRelations (h2X i) = h2CachedX i := by
    rfl
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  simpa only [map_mul, map_pow, map_zero, hm] using h2CachedRelation859

-- Unique local-carrier names avoid private-name collisions with the cached certificate module.
private def sourceH2X (i : Fin generators.count) :
    nativeAlgebra generators.count archiveSourceRelations :=
  nativeProjection generators.count archiveSourceRelations (MvPolynomial.X i)
private theorem sourceH2Relation2 :
    (sourceH2X ⟨1,by decide⟩)^3 +
      (sourceH2X ⟨0,by decide⟩)^2 * (sourceH2X ⟨2,by decide⟩) = 0 := by
  have hm (i : Fin generators.count) :
      nativeEquiv generators.count archiveSourceRelations (sourceH2X i) = h2CachedX i := by
    rfl
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  simpa only [map_add, map_mul, map_pow, map_zero, hm] using h2CachedRelation2
private theorem sourceH2Relation859 :
    (sourceH2X ⟨1,by decide⟩)^2 * (sourceH2X ⟨79,by decide⟩) = 0 := by
  have hm (i : Fin generators.count) :
      nativeEquiv generators.count archiveSourceRelations (sourceH2X i) = h2CachedX i := by
    rfl
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  simpa only [map_mul, map_pow, map_zero, hm] using h2CachedRelation859

private theorem h2SourceZero (x : sourceData.component 13 135) :
    sourceData.product 1 4 13 135 (sourceData.atom .h2) x = 0 := by
  apply Subtype.ext
  change nativeProjection generators.count archiveSourceRelations
    (MvPolynomial.X ⟨2,by decide⟩) * x.val = 0
  apply (nativeEquiv generators.count archiveSourceRelations).injective
  have h := h2RawZero
    (nativePartToCached generators.count generators.degree archiveSourceRelations 13 135 x)
  change CachedStandard.nativeProjection generators.count archiveSourceRelations
    (MvPolynomial.X ⟨2, by decide⟩) *
      nativeEquiv generators.count archiveSourceRelations x.val = 0 at h
  simpa only [map_mul, nativeEquiv_projection, map_zero] using h

end
end KIP126.Computation.Table.Internal
