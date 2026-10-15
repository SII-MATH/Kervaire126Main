module

public import KIP126.Main.Computation.LinCoordinates.Certificates.SquareDetection.Data
public import KIP126.Def.ComputationModel.Parsing.NaturalNumbers

@[expose] public section

namespace KIP126.LinE2.SquareDetection

def charsMonomialOrder (cs : List Char) : ℕ :=
  if cs = [] then 0
  else orderOfPowers ((cs.splitOn ',').map (fun ns => (charsToNat? ns).getD 0))

def charsRelationCheck (cs : List Char) : Bool :=
  (cs.splitOn ';').all (fun m => decide (3 ≤ charsMonomialOrder m))

def charsChunkCheck (cs : List Char) : Bool :=
  (cs.splitOn '\n').all charsRelationCheck

/-- The finite family of character-list certificates, still evaluated on the
original archived strings. -/
def chunksCheck (chunks : List String) : Bool :=
  chunks.all (fun s => charsChunkCheck s.toList)

end KIP126.LinE2.SquareDetection
