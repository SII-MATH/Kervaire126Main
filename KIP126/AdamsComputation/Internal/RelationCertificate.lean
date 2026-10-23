module

public meta import Lean.Elab.Tactic
import Mathlib.Data.List.Basic
import all Init.Data.List.SplitOn.Basic

/-! Pure finite checker and proof-producing quotation tactic. The host string
reader supplies data only: Eq.refl and decide +kernel certify every output.
The balanced character expression keeps ordinary build stack use bounded. -/

@[expose] section
namespace KIP126.Computation.RelationCertificate
meta section
open Lean Elab Tactic Meta
unsafe def evalString (e : Expr) : MetaM String := evalExpr String (mkConst ``String) e
private partial def balancedChars (cs : List Char) : Expr :=
  if cs.length ≤ 128 then
    let charTy := mkConst ``Char
    let cons := mkApp (mkConst ``List.cons [.zero]) charTy
    cs.reverse.foldl (fun acc c => mkApp2 cons (toExpr c) acc)
      (mkApp (mkConst ``List.nil [.zero]) charTy)
  else
    mkApp3 (mkConst ``List.append [.zero]) (mkConst ``Char)
      (balancedChars (cs.take (cs.length/2))) (balancedChars (cs.drop (cs.length/2)))
private def certifyRelationChunk (value : TSyntax `term) : TacticM Unit := do
  let e ← Term.elabTerm value (some (mkConst ``String))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let s ← unsafe evalString e
  let cs := balancedChars s.toList
  let rhs := mkApp (mkConst ``String.ofList) cs
  let heq ← mkEq e rhs
  let pf ← mkEqRefl e
  let g ← getMainGoal
  let g ← g.assert `hcert heq pf
  let (_,g) ← g.intro1P
  replaceMainGoal [g]
  evalTactic (← `(tactic| rw [$(mkIdent `hcert):term, String.toList_ofList]))
  evalTactic (← `(tactic| decide +kernel))
end

private def charsIsNat (cs : List Char) : Bool := Id.run do
  let mut lastWasDigit := false
  for c in cs do
    if c = '_' then
      if !lastWasDigit then return false
      lastWasDigit := false
    else if c.isDigit then lastWasDigit := true
    else return false
  return lastWasDigit
private def charsToNat (cs : List Char) : Nat :=
  if charsIsNat cs then cs.foldl (fun n c => if c = '_' then n else n*10+(c.toNat-'0'.toNat)) 0 else 0
def coeffPowers (n : ℕ) (target : List (Fin n)) : List ℕ → Bool
  | [] => target.isEmpty
  | i :: a :: rest =>
      if h : i < n then
        if a = 0 then coeffPowers n target rest
        else if a = 1 && target.contains ⟨i,h⟩ then
          coeffPowers n (target.erase ⟨i,h⟩) rest
        else false
      else false
  | [_] => false

private def coeffChars (n : ℕ) (target : List (Fin n)) (cs : List Char) : Bool :=
  if cs.isEmpty then target.isEmpty else coeffPowers n target ((cs.splitOn ',').map charsToNat)
private def rowCount (n : ℕ) (targets : List (List (Fin n))) (cs : List Char) : ℕ :=
  ((cs.splitOn ';').map fun mon => ((targets.map fun target => if coeffChars n target mon then 1 else 0).sum)).sum

def top : List (List (Fin 2914)) := [[1,7,275],[4,320],[7,287],[70,98]]
def proper : List (List (Fin 2914)) := [[],[1],[7],[275],[1,7],[1,275],[7,275],[4],[320],[287],[70],[98]]
def allowed : List Nat := [1,7,275,4,320,287,70,98]
def badOutside (allowed : List Nat) : List Nat → Bool
  | i::a::xs => (!(allowed.contains i) && decide (0<a)) || badOutside allowed xs
  | _ => false
def monCountGood (cs : List Char) : Nat × Bool :=
  if cs.isEmpty then (0,false) else
    let ns := (cs.splitOn ',').map charsToNat
    if badOutside allowed ns then (0,true) else
      ((top.map (fun ts => if coeffPowers 2914 ts ns then 1 else 0)).sum,
        proper.all (fun ts => !(coeffPowers 2914 ts ns)))
def good (cs : List Char) : Bool :=
  let vals := (cs.splitOn ';').map monCountGood
  decide ((vals.map Prod.fst).sum % 2 = 0) && vals.all Prod.snd

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

end KIP126.Computation.RelationCertificate
end
