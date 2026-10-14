module

public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section


/-! Short, reusable names for the actual page-level computation predicates.
These are definitional aliases: unfolding them recovers the full
representative, degree-transport and nonzero-target obligations. -/

namespace KIP126.Core.SpectralSequence

universe u v

abbrev Differential
    {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) {p q : ℤ × ℤ}
    (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  HasDifferential E r p q x y

abbrev NonzeroDifferential
    {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) {p q : ℤ × ℤ}
    (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  HasNonzeroDifferential E r p q x y

end KIP126.Core.SpectralSequence
