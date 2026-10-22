module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.ClosedBall
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory Metric Set HomotopyExtension
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual full cube-boundary inclusion has homotopy extension,
transported through the specified maximum-norm disk homeomorphism. -/
theorem cubeBoundaryInclusion_hasHomotopyExtension (n : ℕ) :
    HasHomotopyExtension (cubeBoundaryInclusion.{u} n) := by
  intro Y f p hp
  let e := cubeClosedBallHomeomorph n
  let c : C(closedBall (0 : Fin n → ℝ) 1,cubeObject.{u} n) :=
    ⟨fun x => ULift.up (e.symm x),continuous_uliftUp.comp e.symm.continuous⟩
  have hb (x : sphere (0 : Fin n → ℝ) 1) :
      e.symm ⟨x.val,sphere_subset_closedBall x.property⟩ ∈ _root_.Cube.boundary (Fin n) := by
    apply (cubeClosedBallHomeomorph_boundary n _).mpr
    rw [show cubeClosedBallHomeomorph n = e from rfl,e.apply_symm_apply]
    simpa only [mem_sphere,dist_zero_right] using x.property
  let b : C(sphere (0 : Fin n → ℝ) 1,cubeBoundaryObject.{u} n) :=
    ⟨fun x => ULift.up ⟨e.symm ⟨x.val,sphere_subset_closedBall x.property⟩,hb x⟩,
      continuous_uliftUp.comp ((e.symm.continuous.comp
        (continuous_subtype_val.subtype_mk (fun x => sphere_subset_closedBall x.property))).subtype_mk hb)⟩
  let p' : C(sphere (0 : Fin n → ℝ) 1 × I,Y) :=
    p.comp ⟨fun z => (b z.1,z.2),(b.continuous.comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨H,hH₀,hHb⟩ := Ball.boundary_homotopy_extension (f.comp c) p'
    (fun x => hp (b x))
  refine ⟨H.comp ⟨fun z => (e z.1.down,z.2),
    (e.continuous.comp (continuous_uliftDown.comp continuous_fst)).prodMk continuous_snd⟩,?_,?_⟩
  · intro x
    exact (hH₀ (e x.down)).trans (congrArg f (congrArg ULift.up (e.symm_apply_apply x.down)))
  · intro x t
    let y : sphere (0 : Fin n → ℝ) 1 :=
      ⟨(e x.down.val).val,by
        rw [mem_sphere,dist_zero_right]
        exact (cubeClosedBallHomeomorph_boundary n x.down.val).mp x.down.property⟩
    have hby : b y = x := by
      apply ULift.ext
      apply Subtype.ext
      exact e.symm_apply_apply x.down.val
    exact (hHb y t).trans (congrArg (fun a => p (a,t)) hby)

end KIP126.Topology.HomotopyLifting
