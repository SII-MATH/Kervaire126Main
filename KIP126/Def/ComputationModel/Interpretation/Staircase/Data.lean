module

public import KIP126.Def.ComputationModel.Raw.Staircase.Data

@[expose] public section

/-!
# Deterministic sphere-staircase decoding

Only the fixed ordinary Adams staircase is decoded here. These levels
are not log page codes or cofiber-sequence levels. `SetDiffSc`
(`ss.cpp:281–328`) stores an unresolved d_r at level 10000-r;
a zero d_r advances that bound to r+1. `SetImageSc` (:374–436)
stores membership in boundaries through r when its source is unknown.
Level 9000 is the program's threshold 1000, retained as a finite bound.
The decoder does not manufacture nonvanishing, E∞ survival, or a
particular hitting differential from either unknown value.
-/

namespace KIP126.Computation.LinCalculations.Staircase

open Raw

/-- Reject malformed and noncanonical coordinates. An empty string is
the zero vector. SQL NULL and -1 are handled separately as unknowns. -/
def parseCoordinates (text : String) : Option (List Nat) := do
  if text.isEmpty then return []
  let values ← (text.splitOn ",").mapM String.toNat?
  if values == values.mergeSort (· ≤ ·) && values == values.eraseDups then
    return values
  else none

/-- A concrete finite equation, a cycle bound, or an incoming boundary
bound. The two bounds deliberately carry no nonzero assertion. -/
inductive Claim where
  | equation (r s t : Nat) (x dx : List Nat)
  | reaches (r s t : Nat) (x : List Nat)
  | boundaryBy (r s t : Nat) (x : List Nat)
  deriving Repr, DecidableEq, BEq

/-- SQL NULL is the snapshot reader's unknown differential. The raw
row continues to distinguish it from the explicit unknown encoding. -/
def unknownDiff : Option String → Bool
  | none => true
  | some "-1" => true
  | some "[NULL]" => true
  | _ => false

/-- Decode a staircase row with nonnegative coordinates and target degree
in range. Unsupported levels or encodings return `none`. Coverage of the
fixed table and truth of its interpreted statements are separate conditions. -/
def decode (row : StaircaseRow) : Option Claim := do
  let s ← row.s
  let t ← row.t
  if s < 0 || t < 0 || 261 < t then none else do
    let x ← parseCoordinates (← row.base)
    let level ← row.level
    if level == 9000 then
      return .reaches 1000 s.toNat t.toNat x
    else if 9000 < level && level ≤ 9998 then
      let r := 10000 - level
      if unknownDiff row.diff then
        return .reaches r.toNat s.toNat t.toNat x
      else
        let dx ← parseCoordinates (← row.diff)
        if t + r - 1 ≤ 261 then
          return .equation r.toNat s.toNat t.toNat x dx
        else none
    else if 2 ≤ level && level < 999 then
      if unknownDiff row.diff then
        return .boundaryBy level.toNat s.toNat t.toNat x
      else
        let source ← parseCoordinates (← row.diff)
        if level ≤ s && level - 1 ≤ t then
          return .equation level.toNat (s - level).toNat (t - level + 1).toNat source x
        else none
    else none

end KIP126.Computation.LinCalculations.Staircase
