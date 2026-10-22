module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Data

@[expose] section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory
open scoped unitInterval

universe u

/-- Actual homotopy extension along a map, with all target spaces and
all compatible continuous families quantified explicitly. -/
def HasHomotopyExtension {A B : TopCat.{u}} (i : A ⟶ B) : Prop :=
  ∀ (Y : TopCat.{u}) (f : C(B, Y)) (p : C(A × I, Y)),
    (∀ a, p (a, 0) = f (i a)) →
      ∃ H : C(B × I, Y),
        (∀ b, H (b, 0) = f b) ∧ (∀ a t, H (i a, t) = p (a, t))

end KIP126.Topology.HomotopyExtension
