module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Iteration.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.ClosedBall.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Reindex
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.ClosedBall
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual cube--whole-boundary pair is the realization of an
explicit finite-order cone--base pair, in every universe and dimension.
Dimension zero is included: its boundary order is empty. -/
theorem exists_orderBoundaryCone_cube_homeomorph (n : ℕ) :
    ∃ b : |nerve (orderProperChains (ULift.{u} (Fin (n+1))))| ≃ₜ cubeBoundaryObject.{u} n,
      ∃ c : |nerve (WithTop (orderProperChains (ULift.{u} (Fin (n+1)))))| ≃ₜ cubeObject.{u} n,
        ∀ x, c (SSet.toTop.map (orderMappingConeSourceTopInclusion
          (orderProperChains (ULift.{u} (Fin (n+1))))) x) = cubeBoundaryInclusion n (b x) := by
  let P := ULift.{u} (Fin (n+1))
  let r := Simplex.reindexHomeomorph (Equiv.ulift : P ≃ Fin (n+1))
  obtain ⟨s,hs⟩ := Simplex.exists_stdSimplex_closedBall_homeomorph n
  let e := r.trans (s.trans (cubeClosedBallHomeomorph n).symm)
  have he (x : stdSimplex ℝ P) :
      (∃ p, x p = 0) ↔ e x ∈ _root_.Cube.boundary (Fin n) := by
    rw [cubeClosedBallHomeomorph_boundary]
    change (∃ p, x p = 0) ↔ ‖(cubeClosedBallHomeomorph n
      ((cubeClosedBallHomeomorph n).symm (s (r x)))).val‖ = 1
    rw [Homeomorph.apply_symm_apply]
    exact (Simplex.reindexHomeomorph_boundary (Equiv.ulift : P ≃ Fin (n+1)) x).trans (hs (r x))
  obtain ⟨b,hb⟩ := exists_orderBoundary_stdSimplex_homeomorph P
  obtain ⟨c,_,hc,_⟩ := exists_orderBoundaryCone_stdSimplex_homeomorph P
  let B := (b.trans (e.subtype he)).trans (Homeomorph.ulift.symm)
  let C := (c.trans e).trans (Homeomorph.ulift.symm)
  refine ⟨B,C,?_⟩
  intro x
  apply ULift.ext
  change e (c (SSet.toTop.map (orderMappingConeSourceTopInclusion _) x)) = e (b x).val
  apply congrArg e
  exact (hc x).trans (hb x).symm

end KIP126.Topology.SimplicialRealization
