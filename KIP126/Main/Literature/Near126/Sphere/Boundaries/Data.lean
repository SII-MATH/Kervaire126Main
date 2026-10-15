module

public import KIP126.Main.Literature.Near126.Sphere.Predicates

@[expose] public section


namespace KIP126.Computation.Near126
open KIP126.LinE2 KIP126.Classical.Adams KIP126.SpectralSequence


attribute [local irreducible] KIP126.LinE2.homogeneousPart

/-- The two d₂-boundary statements used in `prop:state5false` of AimPaper.
The differential sources have bidegrees (10,136) and (11,137); the targets
are the fixed products Ph₂ and Qh₂. These conditions require actual
boundaries in the sphere Adams sequence, in addition to the E₂ products.

Boundary membership also applies to zero products and linear combinations.
The synthetic filtration consequences and the exhaustion of P/Q candidates
are separate statements. -/
structure SphereBoundaryFacts where
  p_h2_d2_boundary :
    (IsPageBoundary sphereAdamsData 2 (10, 136)
      (linToSphereE2 12 137 (by decide) (mulAt P (atom .h2))))
  q_h2_d2_boundary :
    (IsPageBoundary sphereAdamsData 2 (11, 137)
      (linToSphereE2 13 138 (by decide) (mulAt Q (atom .h2))))

end KIP126.Computation.Near126
