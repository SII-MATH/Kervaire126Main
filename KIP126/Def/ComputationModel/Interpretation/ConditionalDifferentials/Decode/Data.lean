module

public import KIP126.Def.ComputationModel.Raw.Data

@[expose] public section

/-!
# Retained branch syntax in the pinned Lin log

Source: `v126.3.cw49`, `ss/deduce.cpp:329–389` and
`ss/mylog.cpp:120–148,151–206`. `TryDiff` deletes noncontradictory attempts;
retained T/TI rows are assumptions of attempted refutations, not conclusions.
The raw artifact has no `exclusions` table. Neither an exclusion certificate
nor a complete candidate list is reconstructed here.

Rows must be supplied in increasing database-id order. A trial at depth d
replaces the previous trial at that depth; the trials at smaller positive
depths are its enclosing context. Missing parents are reported, not invented.
Every output retains the complete raw row, including nullable/multiline info.
-/

namespace KIP126.Computation.LinCalculations.ConditionalDifferentials

open Raw

inductive Direction where
  | forward | inverse
  deriving Repr, DecidableEq, BEq

/-- T stores the source degree; TI stores the TARGET degree. -/
def trialDirection : Option String → Option Direction
  | some "T" => some .forward
  | some "TI" => some .inverse
  | _ => none

/-- The retained conditional deduction codes. This does not decode any of
the other reason families or turn a NULL-reason hint into a conclusion. -/
def deductionDirection : Option String → Option Direction
  | some "D" => some .forward
  | some "DI" => some .inverse
  | _ => none

structure TrialFrame where
  row : LogRow
  depth : Nat
  direction : Direction
  deriving Repr, DecidableEq, BEq

inductive ScopeIssue where
  | nonIncreasingId
  | missingDepth
  | trialAtRoot
  | missingParent (required available : Nat)
  deriving Repr, DecidableEq, BEq

inductive RowScope where
  | metadata
  /-- The context excludes the new trial itself. For a nontrial row it is
  the entire enclosing assumption stack, including the current depth. -/
  | scoped (context : List TrialFrame) (trial : Option Direction)
  | unresolved (issue : ScopeIssue)
  deriving Repr, DecidableEq, BEq

structure ScopedRow where
  row : LogRow
  scope : RowScope
  deriving Repr, DecidableEq, BEq

structure ScopeState where
  lastId : Option Int := none
  frames : List TrialFrame := []
  deriving Repr, DecidableEq, BEq

/-- One deterministic stack transition. Metadata and invalid rows clear
the active stack; they cannot silently provide a missing trial assumption. -/
def scopeStep (state : ScopeState) (row : LogRow) : ScopeState × ScopedRow := Id.run do
  let cleared : ScopeState := ⟨some row.id, []⟩
  if state.lastId.any (fun i => row.id ≤ i) then
    return (cleared, ⟨row, .unresolved .nonIncreasingId⟩)
  let some depth := row.depth
    | return (cleared, ⟨row, .unresolved .missingDepth⟩)
  if depth < 0 then
    return (cleared, ⟨row, .metadata⟩)
  let d := depth.toNat
  match trialDirection row.reason with
  | some direction =>
      if d = 0 then
        return (cleared, ⟨row, .unresolved .trialAtRoot⟩)
      let parents := state.frames.take (d - 1)
      if parents.length != d - 1 then
        return (cleared, ⟨row, .unresolved (.missingParent (d - 1) parents.length)⟩)
      let frame : TrialFrame := ⟨row, d, direction⟩
      return (⟨some row.id, parents ++ [frame]⟩, ⟨row, .scoped parents (some direction)⟩)
  | none =>
      let context := state.frames.take d
      if context.length != d then
        return (cleared, ⟨row, .unresolved (.missingParent d context.length)⟩)
      return (⟨some row.id, context⟩, ⟨row, .scoped context none⟩)

/-- Lossless scoped view of the retained rows, in their input order.
Successful scoping asserts only syntax, never branch refutation. -/
def scopeRows (rows : List LogRow) : List ScopedRow :=
  ((rows.foldl (fun (acc : ScopeState × List ScopedRow) row =>
    let next := scopeStep acc.1 row
    (next.1, next.2 :: acc.2)) (⟨none, []⟩, [])).2).reverse

inductive CoordinateIssue where
  | sqlNull
  | unknown (text : String)
  | malformed (text : String)
  deriving Repr, DecidableEq, BEq

/-- Decode only explicit decimal coordinate lists. The empty string is
zero; SQL NULL and the unknown sentinels are failures of this finite decoder.
The raw row remains available even on failure. Basis-range validation is
the responsibility of the actual partial coordinate dictionary. -/
def decodeCoordinates (text : Option String) : Except CoordinateIssue (List Nat) := do
  match coordinateCode text with
  | .sqlNull => throw .sqlNull
  | .zero => return []
  | .unknownSentinel text => throw (.unknown text)
  | .encoded text =>
      (text.splitOn ",").mapM fun token => do
        let some n := token.toNat? | throw (.malformed text)
        if toString n = token then return n else throw (.malformed text)

inductive EquationIssue where
  | unsupportedReason
  | missingName
  | missingDegree
  | inconsistentStem
  | notFinitePage (code : PageCode)
  | sourceCoordinates (issue : CoordinateIssue)
  | targetCoordinates (issue : CoordinateIssue)
  deriving Repr, DecidableEq, BEq

/-- A syntactically normalized equation payload. This structure is not a
mathematical fact. In particular its two coordinate lists may denote zero. -/
structure RawEquation where
  row : LogRow
  direction : Direction
  name : String
  r : Int
  sourceDegree : Int × Int
  targetDegree : Int × Int
  sourceIndices : List Nat
  targetIndices : List Nat
  deriving Repr, DecidableEq, BEq

/-- The direction is supplied by a reviewed reason family. The coordinates
`x` and `dx` always mean source and target respectively; only the stored
DEGREE switches in an inverse row (`mylog.cpp:181–206`). Codes 999, 1000,
1001 and unknown coordinates are never coerced into finite equations. -/
def normalizeFiniteEquation (direction : Direction) (row : LogRow) :
    Except EquationIssue RawEquation := do
  let some name := row.name | throw .missingName
  let (some s, some t) := (row.s, row.t) | throw .missingDegree
  if row.stem.any (fun n => n != t - s) then throw .inconsistentStem
  let .ordinaryCandidate page := pageCode row.r
    | throw (.notFinitePage (pageCode row.r))
  let x ← (decodeCoordinates row.x).mapError EquationIssue.sourceCoordinates
  let y ← (decodeCoordinates row.dx).mapError EquationIssue.targetCoordinates
  let r : Int := page
  let (source, target) := match direction with
    | .forward => ((s, t), (s + r, t + (r - 1)))
    | .inverse => ((s - r, t - (r - 1)), (s, t))
  return ⟨row, direction, name, r, source, target, x, y⟩

def decodeTrialEquation (row : LogRow) : Except EquationIssue RawEquation := do
  let some direction := trialDirection row.reason | throw .unsupportedReason
  normalizeFiniteEquation direction row

def decodeDeductionEquation (row : LogRow) : Except EquationIssue RawEquation := do
  let some direction := deductionDirection row.reason | throw .unsupportedReason
  normalizeFiniteEquation direction row

end KIP126.Computation.LinCalculations.ConditionalDifferentials
