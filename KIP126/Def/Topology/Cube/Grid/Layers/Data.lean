module

public import KIP126.Def.Topology.Cube.Grid.Incidence.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The bottom and all spatial boundary faces of a homotopy cube. -/
def gridGlobalHorn (n : ℕ) : Set (Fin (n+1) → I) :=
  {x | x 0 = 0 ∨ ∃ i : Fin n, x i.succ = 0 ∨ x i.succ = 1}

/-- The already prescribed horn together with the earlier grid layers. -/
def gridPast (n m r : ℕ) : Set (Fin (n+1) → I) :=
  gridGlobalHorn n ∪ {x | ∃ k : Fin (n+1) → Fin (m+1),
    gridDegree k < r ∧ x ∈ gridCell (n+1) m k}

/-- On each new cell all lower spatial faces are incoming; an upper
spatial face is incoming precisely when it is a global boundary face. -/
def gridIncomingFaces {n m : ℕ} (k : Fin (n+1) → Fin (m+1)) :
    Set (Fin n × Bool) :=
  {q | q.2 = false ∨ (k q.1.succ).val = m}

/-- Incoming faces in affine cube coordinates, including the time bottom. -/
def gridIncoming {n m : ℕ} (k : Fin (n+1) → Fin (m+1)) :
    Set (Fin (n+1) → I) :=
  {x | x 0 = 0 ∨ ∃ i : Fin n,
    x i.succ = 0 ∨ (k i.succ).val = m ∧ x i.succ = 1}

end KIP126.Topology.Cube
