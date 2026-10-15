module

public import KIP126.Main.Literature.Near126.Sphere.Boundaries.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs

@[expose] public section

namespace KIP126.Computation.Near126
open KIP126.LinE2 KIP126.Classical.Adams KIP126.SpectralSequence

attribute [local irreducible] KIP126.LinE2.homogeneousPart

/-- The first product's actual d₂ vanishes by d₂²=0, not by an independent
postulate about a coordinate differential. -/
theorem SphereBoundaryFacts.p_h2_is_d2_cycle (F : SphereBoundaryFacts) :
    IsPageCycle sphereAdamsData 2 (12, 137)
      (linToSphereE2 12 137 (by decide) (mulAt P (atom .h2))) := by
  exact F.p_h2_d2_boundary.isCycle

theorem SphereBoundaryFacts.q_h2_is_d2_cycle (F : SphereBoundaryFacts) :
    IsPageCycle sphereAdamsData 2 (13, 138)
      (linToSphereE2 13 138 (by decide) (mulAt Q (atom .h2))) := by
  exact F.q_h2_d2_boundary.isCycle

end KIP126.Computation.Near126
