module

public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

/-!
Weak contractibility of an actual topological space, stated using its homotopy
sets in every finite degree. Mathlib's `HomotopyGroup.pi0EquivZerothHomotopy`
identifies degree zero with the set of path components; it must not be omitted.
This condition does not assert a homotopy equivalence to a point, and no
comparison with a model of a derived moduli space is implicit in it.
-/

namespace KIP126.Topology

universe u

/-- A weakly contractible space is nonempty and has singleton homotopy sets
at every base point in all degrees, including degree zero. The nonemptiness
clause rules out the vacuous assertion for the empty space; degree zero
requires a single path component. For positive degrees the same condition
says that every homotopy group is trivial. -/
def WeaklyContractibleSpace (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty X ∧ ∀ (x : X) (n : ℕ), Subsingleton (HomotopyGroup.Pi n X x)

end KIP126.Topology
