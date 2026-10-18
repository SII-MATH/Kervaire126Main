module

public import KIP126.SpectralSequence.Computation.Predicates
import all KIP126.SpectralSequence.Computation.Predicates

@[expose] section


/-! Short, reusable names for the actual page-level computation predicates.
These are definitional aliases: unfolding them recovers the full
representative, degree-transport and nonzero-target obligations. -/

namespace KIP126.Core.SpectralSequence

universe u v

public abbrev Differential
    {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) {p q : ℤ × ℤ}
    (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  HasDifferential E r p q x y

public abbrev NonzeroDifferential
    {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) {p q : ℤ × ℤ}
    (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  HasNonzeroDifferential E r p q x y

end KIP126.Core.SpectralSequence
