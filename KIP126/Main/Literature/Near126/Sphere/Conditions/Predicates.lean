module

public import KIP126.Main.Literature.Near126.Sphere.Predicates

@[expose] public section

namespace KIP126.Computation.Near126.Sphere
open KIP126.Classical.Adams KIP126.SpectralSequence

/-- Condition (3) of prop:possible_h_6_sq, on the fixed sphere. Survival to E₆
is explicit, so absence of representatives cannot make this condition true.
The vanishing applies to every continuation of the specified E₂ class. -/
def Stem126D6Vanishes : Prop :=
  Survival 6 W ∧
    DifferentialVanishesOn sphereAdamsData 6 (8, 134)
      (linToSphereE2 8 134 (by decide) W)

/-- The nonzero d₁₂ alternative in prop:possible_h_6_sq. Both classes and the
differential belong to the very sequence used in the final target. This
definition does not assert that the alternative occurs or is exhaustive. -/
def H6SquareSupportsD12 : Prop :=
  HasNonzeroDifferential sphereAdamsData 12 (2, 128) (14, 139)
    computedH6Square (linToSphereE2 14 139 (by decide) T)

end KIP126.Computation.Near126.Sphere
