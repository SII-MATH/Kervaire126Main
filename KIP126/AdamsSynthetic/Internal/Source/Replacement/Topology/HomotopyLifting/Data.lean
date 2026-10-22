module

import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval
universe u

/-- The bottom and prescribed side of an actual homotopy cylinder. -/
def CylinderHorn (Z : Type u) (S : Set Z) :=
  {z : I × Z // z.1 = 0 ∨ z.2 ∈ S}

instance {Z : Type u} [TopologicalSpace Z] (S : Set Z) :
    TopologicalSpace (CylinderHorn Z S) :=
  inferInstanceAs (TopologicalSpace (Subtype _))

/-- The full boundary of the product of an interval and a pair. -/
def cylinderBoundary {Z : Type u} (S : Set Z) : Set (I × Z) :=
  {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}

/-- Insert the homotopy parameter as the first coordinate of a finite cube. -/
def cubeCylinderHomeomorph (n : ℕ) :
    (I × (Fin n → I)) ≃ₜ (Fin (n + 1) → I) where
  toFun z := Fin.cons z.1 z.2
  invFun u := (u 0,fun i => u i.succ)
  left_inv _ := rfl
  right_inv u := by ext i; induction i using Fin.cases <;> rfl
  continuous_toFun := continuous_pi fun i => by
    induction i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk
    (continuous_pi fun i => continuous_apply i.succ)

end KIP126.Topology.HomotopyLifting
