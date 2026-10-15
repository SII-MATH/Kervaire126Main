module

public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs
public import Mathlib.Topology.CWComplex.Abstract.Basic

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set Metric

universe u

set_option backward.isDefEq.respectTransparency false

/-- The standard simplex is a Euclidean disk as a pair with its geometric
boundary. The norm change is performed by radial rescaling of a convex body. -/
theorem exists_stdSimplex_euclideanBall_homeomorph (n : ℕ) :
    ∃ e : stdSimplex ℝ (Fin (n+1)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ x, (∃ i, x.1 i = 0) ↔ ‖(e x).1‖ = 1 := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  let S : Set (EuclideanSpace ℝ (Fin n)) := L '' Simplex.coordinateSimplex n
  have hSc : Convex ℝ S := (Simplex.coordinateSimplex_convex n).linear_image L.toLinearMap
  have hSn : (interior S).Nonempty := by
    change (interior (L.toHomeomorph '' Simplex.coordinateSimplex n)).Nonempty
    rw [← L.toHomeomorph.image_interior]
    exact (Simplex.coordinateSimplex_interior_nonempty n).image L
  have hSk : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Simplex.coordinateSimplex_isClosed n, Simplex.coordinateSimplex_isBounded n⟩).image L.continuous
  obtain ⟨h,hi,hc,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    hSc hSn hSk.isBounded
  rw [hSk.isClosed.closure_eq] at hc
  have hs : ∀ x, x ∈ Simplex.coordinateSimplex n ↔
      h (L x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x
    rw [← hc]
    exact (h.injective.mem_set_image.trans L.injective.mem_set_image).symm
  let e := (Simplex.coordinateHomeomorph n).trans ((L.toHomeomorph.trans h).subtype hs)
  refine ⟨e,?_⟩
  intro x
  rw [← Simplex.coordinateHomeomorph_mem_frontier]
  have hx : h (L (Simplex.coordinateHomeomorph n x).1) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↔
      (Simplex.coordinateHomeomorph n x).1 ∈ frontier (Simplex.coordinateSimplex n) := by
    rw [← hf]
    change _ ∈ h '' frontier (L.toHomeomorph '' Simplex.coordinateSimplex n) ↔ _
    rw [← L.toHomeomorph.image_frontier]
    exact h.injective.mem_set_image.trans L.injective.mem_set_image
  simpa [e,Metric.mem_sphere] using hx.symm

/-- The realized simplex-boundary arrow is isomorphic to the genuine
Euclidean sphere-to-disk inclusion, rather than merely having isomorphic
source and target spaces. -/
theorem nonempty_boundary_realization_disk_arrow_iso (n : ℕ) :
    Nonempty (Arrow.mk (SSet.toTop.map (∂Δ[n].ι)) ≅
      Arrow.mk (TopCat.diskBoundaryInclusion.{u} n)) := by
  obtain ⟨e,he⟩ := exists_stdSimplex_euclideanBall_homeomorph n
  obtain ⟨b,hb⟩ := exists_boundary_realization_homeomorph.{u} n
  let q : {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 // ‖x.1‖ = 1} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    { toFun := fun x => ⟨x.1.1, by simpa only [Metric.mem_sphere,dist_zero_right,Function.comp_apply] using x.2⟩
      invFun := fun x => ⟨⟨x.1, Metric.sphere_subset_closedBall x.2⟩,
        by simpa only [Metric.mem_sphere,dist_zero_right,Function.comp_apply] using x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x => by simpa only [Metric.mem_sphere,dist_zero_right,Function.comp_apply] using x.2)
      continuous_invFun := (continuous_subtype_val.subtype_mk
        (fun x => Metric.sphere_subset_closedBall x.2)).subtype_mk
        (fun x => by simpa only [Metric.mem_sphere,dist_zero_right,Function.comp_apply] using x.2) }
  let d : |(Δ[n] : SSet.{u})| ≃ₜ TopCat.disk.{u} n :=
    (SimplexCategory.toTopHomeo ⦋n⦌).trans (e.trans Homeomorph.ulift.symm)
  let s : |(∂Δ[n] : SSet.{u})| ≃ₜ TopCat.diskBoundary.{u} n :=
    b.trans ((e.subtype he).trans (q.trans Homeomorph.ulift.symm))
  refine ⟨Arrow.isoMk (TopCat.isoOfHomeo s) (TopCat.isoOfHomeo d) ?_⟩
  ext x
  apply ULift.ext
  apply Subtype.ext
  exact congrArg (fun y => (e y).1) (hb x)

end KIP126.Topology.SimplicialRealization
