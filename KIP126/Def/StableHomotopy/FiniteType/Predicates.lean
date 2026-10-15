module

public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

namespace KIP126.StableHomotopy
open Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- A bound on the actual integer-graded stable homotopy groups. -/
def BoundedBelow (X : C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → Subsingleton (HomotopyGroup n X)

/-- Degreewise finite mod-2 homology. Over F2 this is equivalent to finite
dimension; it imposes no F2-vector-space structure on ordinary pi_* X. -/
def FiniteMod2Type (H : Mod2EilenbergMacLane (C := C)) (X : C) : Prop :=
  ∀ n : ℤ, Finite (Mod2Homology H n X)

end KIP126.StableHomotopy
