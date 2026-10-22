module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Proofs
import Mathlib.Topology.CWComplex.Abstract.Basic

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual Euclidean disk boundary map is a closed embedding. -/
theorem diskBoundaryInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n) := by
  letI : T2Space (TopCat.disk.{u} n) :=
    inferInstanceAs (T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
  exact (TopCat.diskBoundaryInclusion n).hom.continuous.isClosedEmbedding
    ((TopCat.mono_iff_injective _).mp inferInstance)

/-- Each relative CW attachment gives a genuine closed embedding of the
preceding skeleton. -/
theorem relativeCWComplex_stage_isClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : TopCat.RelativeCWComplex f) (n : ℕ) :
    IsClosedEmbedding (c.F.map (homOfLE (Nat.le_succ n))) :=
  isClosedEmbedding_of_attachCells (c.attachCells n (by simp))
    (fun _ => diskBoundaryInclusion_isClosedEmbedding n)

/-- Every relative CW skeleton is an actual closed subspace of the
completed cell complex. -/
theorem relativeCWComplex_inclusion_isClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : TopCat.RelativeCWComplex f) (n : ℕ) :
    IsClosedEmbedding (c.incl.app n) :=
  isClosedEmbedding_nat_colimit c.F (Cocone.mk Y c.incl) c.isColimit
    (relativeCWComplex_stage_isClosedEmbedding c) n

/-- An actual relative CW-complex structure proves that its source sits
as a closed embedded subspace in its target. -/
theorem relativeCWComplex_isClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : TopCat.RelativeCWComplex f) :
    IsClosedEmbedding f := by
  rw [← c.fac]
  exact (relativeCWComplex_inclusion_isClosedEmbedding c 0).comp
    (TopCat.homeoOfIso c.isoBot).symm.isClosedEmbedding

end KIP126.Topology
