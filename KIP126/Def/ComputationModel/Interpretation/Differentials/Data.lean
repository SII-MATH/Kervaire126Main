module

@[expose] public section

/-!
Typed records exported from the pinned Lin `proofs.db`. Coordinates are local
additive-basis indices, NOT algebra-generator IDs. `s,t` always denote the
source bidegree after normalizing inverse (`DI`, `GI`) records.
-/
namespace KIP126.Computation.LinCalculations

structure DifferentialRow where
  id : Nat
  reason : String
  s : Nat
  t : Nat
  r : Nat
  x : List Nat
  dx : List Nat
  deriving Repr, DecidableEq, BEq

end KIP126.Computation.LinCalculations
