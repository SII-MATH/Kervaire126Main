module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
The path-space model of a homotopy fiber of an actual continuous map.
The topology is the subspace topology of the product of the source with the
compact-open path space. In particular, the source coordinate is not discrete,
and the endpoint condition retains a path rather than requiring equal points.
No comparison with a derived mapping space is asserted by this construction.
-/

namespace KIP126.Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A point above `y` consists of `x` and an actual continuous path from `f x`
to `y`, with the subspace topology of `X × C(unitInterval, Y)`. -/
def PathHomotopyFiber (f : C(X, Y)) (y : Y) :=
  {z : X × C(unitInterval, Y) // z.2 0 = f z.1 ∧ z.2 1 = y}

namespace PathHomotopyFiber

instance (f : C(X, Y)) (y : Y) : TopologicalSpace (PathHomotopyFiber f y) :=
  inferInstanceAs (TopologicalSpace
    {z : X × C(unitInterval, Y) // z.2 0 = f z.1 ∧ z.2 1 = y})

/-- The same path homotopy fiber bundled as an object of `TopCat`. -/
def space (f : C(X, Y)) (y : Y) : TopCat.{max u v} :=
  TopCat.of (PathHomotopyFiber f y)

end PathHomotopyFiber
end KIP126.Topology
