module

public import KIP126.Def.ComputationModel.Certificates.SquareDetection.Parsing
public import Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Search
import all Init.Data.String.Slice

@[expose] public section

namespace KIP126.LinE2.SquareDetection

/-- Character-list form of the standard natural-number parser's lexical test,
including its underscore convention. -/
def charsAreNat (cs : List Char) : Bool := Id.run do
  let mut lastWasDigit := false
  for c in cs do
    if c = '_' then
      if !lastWasDigit then return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else return false
  return lastWasDigit

def charsToNat? (cs : List Char) : Option Nat :=
  if charsAreNat cs then
    some (cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- Preserve the actual library parser, rather than replacing its semantics
with a second unverified data loader. -/
theorem toNat?_eq_chars (s : String) : s.toNat? = charsToNat? s.toList := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    charsToNat?, charsAreNat, String.Slice.forIn_eq_forIn_toList,
    String.Slice.foldl_eq_foldl_toList, String.copy_toSlice]

end KIP126.LinE2.SquareDetection
