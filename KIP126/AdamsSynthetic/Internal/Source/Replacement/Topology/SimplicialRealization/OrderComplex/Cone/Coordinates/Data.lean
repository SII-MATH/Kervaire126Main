module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCone.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Stars.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open scoped unitInterval

universe u

/-- Actual cone coordinates: scale the base weights and give the remaining
weight to the new maximum. -/
noncomputable def orderConeCoordinates {P : Type u} [Fintype P]
    (t : I) (y : stdSimplex ℝ P) : stdSimplex ℝ (WithTop P) :=
  ⟨fun p => match p with
    | none => (t : ℝ)
    | some p => (1 - (t : ℝ)) * y p,
    by
      rintro (_ | p)
      · exact t.property.1
      · exact mul_nonneg (sub_nonneg.mpr t.property.2) (y.property.1 p),
    by
      change (∑ p : Option P, _) = 1
      rw [Fintype.sum_option]
      simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
      ring⟩

end KIP126.Topology.SimplicialRealization
