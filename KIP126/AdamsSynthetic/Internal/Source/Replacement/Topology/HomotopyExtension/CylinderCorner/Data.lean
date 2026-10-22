module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Data

@[expose] section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory Set
open scoped unitInterval

universe u

/-- The actual closed corner of a cylinder: the original image cylinder
and both full ambient endpoints, with the subspace topology. -/
def cylinderCorner {A B : TopCat.{u}} (i : A ⟶ B) : TopCat.{u} :=
  TopCat.of {q : B × I // q.1 ∈ range i ∨ q.2 = 0 ∨ q.2 = 1}

/-- Literal inclusion of the actual cylinder corner. -/
def cylinderCornerMap {A B : TopCat.{u}} (i : A ⟶ B) :
    cylinderCorner i ⟶ TopCat.of (B × I) :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

end KIP126.Topology.HomotopyExtension
