module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Basis.Data
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

/-!
Coordinates on the fixed CSV quotient, recovered from the actual E₂
coordinates and presentation in the common external hypotheses. The basis
is the one specified there; additivity determines F₂ linearity.
-/

namespace KIP126.LinE2

open KIP126.Algebra KIP126.Classical.Adams

/-- Pull the actual E₂ coordinates back through the specified presentation,
using the same F₂ scalar structures. -/
noncomputable def dataCoordinates (s t : ℕ) (ht : t ≤ 261) :
    E2At s t ≃ₗ[F2] (BasisIndex s t →₀ F2) :=
  let e := (linToSphereE2 s t ht).trans (sphereE2Coordinates s t ht)
  { e.toAddEquiv with map_smul' := ZMod.map_smul e }

/-- The basis recovered from those exact coordinates, with no new choice. -/
noncomputable def dataBasis (s t : ℕ) (ht : t ≤ 261) :
    Module.Basis (BasisIndex s t) F2 (E2At s t) :=
  Module.Basis.ofRepr (dataCoordinates s t ht)

/-- Reference an additive generator by its (s,t,CSV index), with safe failure. -/
noncomputable def basisByCSV? (s t : ℕ) (ht : t ≤ 261) (index : ℕ) :
    Option (E2At s t) :=
  (findBasisIndex? s t index).map (dataBasis s t ht)

end KIP126.LinE2
