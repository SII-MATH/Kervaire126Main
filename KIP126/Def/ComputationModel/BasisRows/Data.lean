module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace KIP126.LinE2

structure BasisRow where
  s : ℕ
  t : ℕ
  index : ℕ
  monomial : String
  deriving Inhabited, Repr, BEq, DecidableEq

def decodeBasisRow (line : String) : Except String BasisRow := do
  let [s, t, index, code] := line.splitOn "|"
    | throw "malformed basis row"
  let some s := s.toNat? | throw "invalid basis filtration"
  let some t := t.toNat? | throw "invalid basis internal degree"
  let some index := index.toNat? | throw "invalid basis index"
  return ⟨s, t, index, code⟩


end KIP126.LinE2
