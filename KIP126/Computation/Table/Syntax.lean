module

/- Pinned finite source syntax/data, bbac1fc05843 (MIT).
Copied from KIP126/LinProgram/Route/Raw.lean without changing records. -/

@[expose] section

/-!
# Section 7 computation slice: syntax

The generated file contains only selected coordinates and result records.
`refutation` is a retained root trial's NEGATED equation, not a differential.
`reaches 1000` is a finite cycle bound, not nonzero permanent survival.
All degrees below are Adams (s,t); all indices are local to a degree.
-/
namespace KIP126.Computation.Table.Raw
public inductive Spectrum where
  | sphere | nuCofiber
  deriving DecidableEq, BEq, Repr
public structure Degree where
  spectrum : Spectrum
  s : Nat
  t : Nat
  monomials : List String
  deriving DecidableEq, BEq, Repr
public inductive Kind where
  | equation | reaches | boundaryBy | refutation
  deriving DecidableEq, BEq, Repr
public structure Claim where
  spectrum : Spectrum
  kind : Kind
  r : Nat
  s : Nat
  t : Nat
  x : List Nat
  ts : Nat
  tt : Nat
  /-- Unused for `reaches`/`boundaryBy`; [] there is not a zero differential. -/
  y : List Nat
  origin : String
  record : Nat
  deriving DecidableEq, BEq, Repr
public structure Product where
  s : Nat
  t : Nat
  sp : Nat
  tp : Nat
  deriving DecidableEq, BEq, Repr
public structure BottomMap where
  s : Nat
  t : Nat
  x : List Nat
  y : List Nat
  deriving DecidableEq, BEq, Repr

/-- Coordinate validation is independent of any mathematical realization.
Missing degree, duplicate/out-of-order indices, and out-of-range indices fail. -/
public def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)

public def coordinatesValid (degrees : List Degree) (o : Spectrum)
    (s t : Nat) (indices : List Nat) : Bool :=
  match degrees.find? (fun d => d.spectrum == o && d.s == s && d.t == t) with
  | none => false
  | some d => indices.all (· < d.monomials.length) && strictlyIncreasing indices

/-- Syntax/degree checking only, not certification of any differential. -/
public def Claim.valid (degrees : List Degree) (c : Claim) : Bool :=
  2 ≤ c.r && coordinatesValid degrees c.spectrum c.s c.t c.x &&
    match c.kind with
    | .reaches | .boundaryBy => true
    | .equation | .refutation => c.ts == c.s + c.r && c.tt == c.t + c.r - 1 &&
        coordinatesValid degrees c.spectrum c.ts c.tt c.y
end KIP126.Computation.Table.Raw
