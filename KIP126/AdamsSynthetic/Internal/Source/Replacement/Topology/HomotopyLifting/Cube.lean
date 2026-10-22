module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.ClosedBall
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Ball.HomotopyExtension.Proofs
import Mathlib.Topology.FiberBundle.Trivialization

@[expose] section

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual radial retraction onto the bottom and all side faces. -/
noncomputable def cubeHornRetraction (n : ℕ) :
    C(I × (Fin n → I), CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n))) := by
  let h := cubeClosedBallHomeomorph n
  let r : C(I × (Fin n → I), closedBall (0 : Fin n → ℝ) 1 × I) :=
    ⟨fun z => Ball.cylinderRetraction (h z.2,z.1),
      Ball.cylinderRetraction_continuous.comp ((h.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  have hr (z : I × (Fin n → I)) :
      (r z).2 = 0 ∨ h.symm (r z).1 ∈ _root_.Cube.boundary (Fin n) := by
    rcases Ball.cylinderRetraction_range (h z.2,z.1) with ht | hz
    · exact Or.inl ht
    · right
      apply (cubeClosedBallHomeomorph_boundary n _).mpr
      change ‖(h (h.symm (r z).1)).val‖ = 1
      rw [h.apply_symm_apply]
      exact hz
  exact ⟨fun z => ⟨((r z).2,h.symm (r z).1),hr z⟩,
    (r.continuous.snd.prodMk (h.symm.continuous.comp r.continuous.fst)).subtype_mk hr⟩


end KIP126.Topology.HomotopyLifting

end

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeHornRetraction_restrict (n : ℕ)
    (z : CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n))) :
    cubeHornRetraction n z.val = z := by
  apply Subtype.ext
  rcases z with ⟨⟨t,z⟩,ht | hz⟩
  · change t = 0 at ht
    subst t
    change ((Ball.cylinderRetraction (cubeClosedBallHomeomorph n z,0)).2,
      (cubeClosedBallHomeomorph n).symm (Ball.cylinderRetraction (cubeClosedBallHomeomorph n z,0)).1) = _
    rw [Ball.cylinderRetraction_bottom,Homeomorph.symm_apply_apply]
  · change ((Ball.cylinderRetraction (cubeClosedBallHomeomorph n z,t)).2,
      (cubeClosedBallHomeomorph n).symm (Ball.cylinderRetraction (cubeClosedBallHomeomorph n z,t)).1) = _
    rw [Ball.cylinderRetraction_side _ ((cubeClosedBallHomeomorph_boundary n z).mp hz),Homeomorph.symm_apply_apply]


/-- A single actual bundle chart lifts a whole cube homotopy, preserving
its prescribed bottom and every prescribed side point exactly. -/
theorem exists_relativeLift_in_trivialization
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) (T : Bundle.Trivialization F f) (n : ℕ)
    (g : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),E))
    (H : C(I × (Fin n → I),B)) (hH : ∀ z, H z ∈ T.baseSet)
    (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ L : C(I × (Fin n → I),E), (∀ z, f (L z) = H z) ∧
      (∀ z, L z.val = g z) := by
  have hg (z : CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n))) : g z ∈ T.source := by
    apply T.mem_source.mpr
    rw [hcomm]
    exact hH z.val
  let gF : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),F) :=
    ⟨fun z => (T (g z)).2, (T.continuousOn_toFun.comp_continuous g.continuous hg).snd⟩
  let L : C(I × (Fin n → I),E) :=
    ⟨fun z => T.invFun (H z,gF (cubeHornRetraction n z)),
      T.continuousOn_invFun.comp_continuous
        (H.continuous.prodMk (gF.continuous.comp (cubeHornRetraction n).continuous))
        (fun z => T.mem_target.mpr (hH z))⟩
  refine ⟨L,fun z => T.proj_symm_apply (T.mem_target.mpr (hH z)),?_⟩
  intro z
  change T.invFun (H z.val,gF (cubeHornRetraction n z.val)) = g z
  rw [cubeHornRetraction_restrict]
  change T.invFun (H z.val,(T (g z)).2) = g z
  rw [← hcomm z]
  exact T.symm_apply_mk_proj (hg z)


end KIP126.Topology.HomotopyLifting

end
