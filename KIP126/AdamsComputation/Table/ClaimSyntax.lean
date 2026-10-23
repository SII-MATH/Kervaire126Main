module

public import KIP126.AdamsComputation.Table.Syntax

/-! Pinned finite computation syntax (bbac1fc05843, MIT). -/

@[expose] section
namespace KIP126.Computation.Table.Raw
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
/-- Syntax/degree checking only, not certification of any differential. -/
public def Claim.valid (degrees : List Degree) (c : Claim) : Bool :=
  2 ≤ c.r && coordinatesValid degrees c.spectrum c.s c.t c.x &&
    match c.kind with
    | .reaches | .boundaryBy => true
    | .equation | .refutation => c.ts == c.s + c.r && c.tt == c.t + c.r - 1 &&
        coordinatesValid degrees c.spectrum c.ts c.tt c.y
end KIP126.Computation.Table.Raw
