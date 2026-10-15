module

public import KIP126.Computation.LinCoordinates.Model.E2.Data
public import KIP126.Def.ComputationModel.BasisRows.Data
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section


/-!
# LinProgram/Model/BasisCatalogue/Data

Fixed-data mathematical model. Recorded catalogue values are not a proved basis or actual-page comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Raw additive-basis catalogue from PR #110, ff39e951, Zenodo 14875701.
Rows are not yet a certified `Module.Basis`. The strict parser reports malformed
input; `basisRows` has an explicit empty fallback, checked in executable tests.
CSV indices are local to a bidegree and are not algebra-generator IDs. -/
namespace KIP126.LinE2

def parseBasisRows : Except String (List BasisRow) :=
  (RawData.basisChunks.toList.flatMap (·.splitOn "\n")).mapM decodeBasisRow

def basisRows : List BasisRow := parseBasisRows.toOption.getD []

/-- The catalogue in CSV order, in Adams (s,t), not (stem,s), coordinates. -/
def basisRowsAt (s t : ℕ) : Array BasisRow :=
  (basisRows.filter (fun row => row.s == s && row.t == t)).toArray

abbrev BasisIndex (s t : ℕ) := Fin (basisRowsAt s t).size

def basisRowAt (s t : ℕ) (i : BasisIndex s t) : BasisRow :=
  (basisRowsAt s t)[i]

/-- Lookup by the original CSV index; absent coordinates return `none`. -/
def findBasisIndex? (s t index : ℕ) : Option (BasisIndex s t) :=
  (List.finRange (basisRowsAt s t).size).find?
    (fun i => (basisRowAt s t i).index == index)

noncomputable def basisValue (row : BasisRow) : E2 :=
  projection (monomialOfString row.monomial)

noncomputable def basisElements (s t : ℕ) : List E2 :=
  (basisRowsAt s t).toList.map basisValue

end KIP126.LinE2
