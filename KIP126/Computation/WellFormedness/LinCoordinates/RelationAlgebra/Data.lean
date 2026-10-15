module

public import KIP126.Computation.WellFormedness.LinCoordinates.E2
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

/-! The algebra on the fixed generators modulo their homogeneous relations.
`LinE2.E2` is its quotient by the additional high-degree truncation relations. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace KIP126.LinE2
open KIP126.Algebra
noncomputable section

/-- Only the original CSV relations, with no artificial high-degree zeros. -/
def relationIdeal : Ideal Poly :=
  Ideal.span {p | ∃ code ∈ RawData.relations, p = relationPolynomial code}

abbrev RelationAlgebra := Poly ⧸ relationIdeal

def relationProjection : Poly →ₐ[F2] RelationAlgebra := Ideal.Quotient.mkₐ F2 relationIdeal

/-- The image of the weighted homogeneous polynomial component. -/
def relationHomogeneousPart (s t : ℕ) : Submodule F2 RelationAlgebra :=
  (MvPolynomial.weightedHomogeneousSubmodule F2 generatorDegree (s,t)).map
    relationProjection.toLinearMap

abbrev RelationAt (s t : ℕ) := ↥(relationHomogeneousPart s t)

theorem relationIdeal_le_definingIdeal : relationIdeal ≤ definingIdeal :=
  Ideal.span_mono (fun _ h => Or.inl h)

/-- The quotient map from the relation algebra to its high-degree truncation. -/
def truncate : RelationAlgebra →ₐ[F2] E2 :=
  Ideal.Quotient.factorₐ F2 relationIdeal_le_definingIdeal

@[simp] theorem truncate_projection (p : Poly) : truncate (relationProjection p) = projection p := rfl

end
end KIP126.LinE2
