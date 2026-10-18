module

import all KIP126.E2Computation.Table.Internal.SourceExpression
import Batteries.Tactic.OpenPrivate
import Lean

/-! Internal consumption of the bounded expression comparison, including invalid
source addresses. The fixed upstream comparison is used, not constructed here. -/
open private sourceValue value_comparison from
  KIP126.E2Computation.Table.Internal.SourceExpression

namespace Tests.Computation.SourceExpression
open CategoryTheory KIP126.Computation KIP126.Computation.Table

example (e : Expression) (ht : e.degree.2 ≤ 261) :
    e.value = Standard.comparison e.degree.1 e.degree.2 ht (sourceValue e) :=
  value_comparison e ht

-- Nested expressions use the total-degree bound without extra source assumptions.
example (a b c : Expression) (ht : ((a.mul b).mul c).degree.2 ≤ 261) :
    ((a.mul b).mul c).value =
      Standard.comparison _ _ ht (sourceValue ((a.mul b).mul c)) :=
  value_comparison _ ht

-- The first invalid index stays invalid, even when the requested degree is bounded.
example : sourceValue (.generator Standard.archive.generators.count 0 0) = 0 := by
  simp [sourceValue]

-- A valid index with a wrong degree is not silently reinterpreted as another class.
example (id s t : ℕ) (ht : t ≤ 261) (hi : id < Standard.archive.generators.count)
    (hd : Standard.archive.generators.degree ⟨id, hi⟩ ≠ (s,t)) :
    sourceValue (.generator id s t) = 0 := by
  simp [sourceValue, ht, hi, hd]

example : sourceValue (.generator 0 1 262) = 0 := by
  simp [sourceValue]

-- Extending source evaluation by zero does not extend the comparison range.
example : True := by
  fail_if_success have _ := value_comparison (.generator 0 1 262) (by decide)
  trivial

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if (`KIP126.LinProgram).isPrefixOf m ||
        (`KIP126.Computation.Internal).isPrefixOf m ||
        (`KIP126.E2Computation.Internal).isPrefixOf m ||
        (`KIP126.Computation).isPrefixOf m ||
        (`KIP126.ProofTools).isPrefixOf m ||
        (`KIP126.AdamsCalculations).isPrefixOf m then
      throwError "expression comparison imported a concrete source model: {m}"
  for declaration in [``sourceValue, ``value_comparison] do
    let info ← getConstInfo declaration
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "expression helper has a direct proof hole: {declaration}"
    for axiomName in ← liftCoreM (collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound, `sorryAx].contains axiomName do
        throwError "expression helper uses an unexpected axiom: {declaration}: {axiomName}"

end Tests.Computation.SourceExpression
