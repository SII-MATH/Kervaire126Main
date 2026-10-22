module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Data

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory
open scoped unitInterval

universe u

/-- The actual finite unit cube, lifted only to the chosen universe. -/
def cubeObject (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (Fin n → I))

/-- The full topological boundary of the actual finite unit cube. -/
def cubeBoundaryObject (n : ℕ) : TopCat.{u} :=
  TopCat.of (ULift.{u} (↥(_root_.Cube.boundary (Fin n))))

/-- The actual inclusion of the full cube boundary. -/
def cubeBoundaryInclusion (n : ℕ) : cubeBoundaryObject.{u} n ⟶ cubeObject.{u} n :=
  TopCat.ofHom ⟨fun x => ULift.up x.down.val,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

end KIP126.Topology.HomotopyLifting
