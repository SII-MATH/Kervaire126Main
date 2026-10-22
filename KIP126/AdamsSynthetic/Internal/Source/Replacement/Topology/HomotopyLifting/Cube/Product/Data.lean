module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u

/-- Split off the first coordinate of the original universe-lifted
cube object, retaining its actual topology in both directions. -/
def cubeObjectSuccHomeomorph (n : ℕ) :
    cubeObject.{u} (n + 1) ≃ₜ I × cubeObject.{u} n where
  toFun x := (x.down 0,ULift.up (fun j => x.down j.succ))
  invFun x := ULift.up (Fin.cases x.1 x.2.down)
  left_inv x := by
    apply ULift.ext
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv x := rfl
  continuous_toFun :=
    ((continuous_apply 0).comp continuous_uliftDown).prodMk
      (continuous_uliftUp.comp (continuous_pi (fun j =>
        (continuous_apply j.succ).comp continuous_uliftDown)))
  continuous_invFun :=
    continuous_uliftUp.comp (continuous_pi (fun j =>
      Fin.cases continuous_fst (fun k =>
        (continuous_apply k).comp (continuous_uliftDown.comp continuous_snd)) j))

end KIP126.Topology.HomotopyLifting
