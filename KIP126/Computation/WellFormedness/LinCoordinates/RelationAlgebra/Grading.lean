module

public import KIP126.Computation.WellFormedness.LinCoordinates.RelationAlgebra.Compatibility
public import KIP126.Def.Algebra.GradedQuotient.Data
public import KIP126.Computation.WellFormedness.LinCoordinates.Certificates.RelationCatalogue.Homogeneity
public import Mathlib.RingTheory.GradedAlgebra.AlgHom

@[expose] public section


/-! The relation algebra is bigraded. Truncation induces an equivalence on
every homogeneous component of internal degree at most 261. -/
namespace KIP126.LinE2
open KIP126.Algebra MvPolynomial
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : GradedAlgebra (weightedHomogeneousSubmodule F2 generatorDegree) :=
  weightedGradedAlgebra F2 generatorDegree

/-- Homogeneity uses all original relations, certified against the original archive. -/
theorem relationIdeal_isHomogeneous :
    relationIdeal.IsHomogeneous (weightedHomogeneousSubmodule F2 generatorDegree) := by
  apply Ideal.homogeneous_span
  rintro p ⟨code, hc, rfl⟩
  exact csv_relation_isWeightedHomogeneous code hc

/-- Every class of the relation algebra has a unique finite homogeneous decomposition. -/
instance relationGradedAlgebra : GradedAlgebra
    (fun d : ℕ × ℕ => relationHomogeneousPart d.1 d.2) :=
  KIP126.Algebra.GradedQuotient.gradedAlgebra
    (weightedHomogeneousSubmodule F2 generatorDegree) relationIdeal relationIdeal_isHomogeneous

/-- The polynomial projection preserves the full bigrading, with no degree cutoff. -/
def relationProjectionGraded :
    GradedAlgHom F2 (weightedHomogeneousSubmodule F2 generatorDegree)
      (fun d : ℕ × ℕ => relationHomogeneousPart d.1 d.2) where
  toAlgHom := relationProjection
  map_mem := by
    intro d p hp
    exact ⟨p, hp, rfl⟩

/-- Removing the artificial high-degree zeros changes no component through degree 261. -/
def truncateAtEquiv (s t : ℕ) (ht : t ≤ 261) : RelationAt s t ≃ₗ[F2] E2At s t :=
  LinearEquiv.ofBijective (truncateAt s t)
    ⟨truncateAt_injective_of_homogeneous relationIdeal_isHomogeneous s t ht,
      truncateAt_surjective s t⟩

end
end KIP126.LinE2
