module
import KIP126.Computation.Standard
import KIP126.Computation.Table.Values

set_option backward.isDefEq.respectTransparency false

/-! Private source evaluation and bounded transport for the existing expression
language. Adapted from the 2026-10-17 Computation session's SourceExpression
helper; no concrete catalogue, quotient model or Program implementation is used.
The fixed comparison, product and unit interfaces retain their registered debts.
Invalid generator indices/degrees follow the existing generatorImage zero cases. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.AdamsSynthetic.Standard
noncomputable section

private def sourceValue : (e : Expression) →
    Standard.sourceData.component e.degree.1 e.degree.2
  | .one => Standard.sourceData.unit
  | .named a => Standard.sourceData.atom a
  | .generator id s t =>
      if _ht : t ≤ 261 then
        if hi : id < Standard.archive.generators.count then
          if hd : Standard.archive.generators.degree ⟨id,hi⟩ = (s,t) then
            (eqToHom (congrArg (fun p : ℕ × ℕ => Standard.sourceData.component p.1 p.2) hd))
              (Standard.sourceGenerator ⟨id,hi⟩)
          else 0
        else 0
      else 0
  | .mul a b => Standard.sourceData.product a.degree.1 a.degree.2
      b.degree.1 b.degree.2 (sourceValue a) (sourceValue b)

private theorem value_comparison (e : Expression) (ht : e.degree.2 ≤ 261) :
    e.value = Standard.comparison e.degree.1 e.degree.2 ht (sourceValue e) := by
  induction e with
  | one => exact Standard.comparison_unit.symm
  | named a => rfl
  | generator id s t =>
    change t ≤ 261 at ht
    change generatorImage id s t = Standard.comparison s t ht
      (sourceValue (.generator id s t))
    dsimp only [generatorImage, sourceValue]
    split_ifs <;> first | rfl | exact (map_zero _).symm
  | mul a b iha ihb =>
    have ha : a.degree.2 ≤ 261 := by change a.degree.2 + b.degree.2 ≤ 261 at ht; omega
    have hb : b.degree.2 ≤ 261 := by change a.degree.2 + b.degree.2 ≤ 261 at ht; omega
    have h := (Standard.comparison_product a.degree.1 a.degree.2 b.degree.1 b.degree.2
      ht (sourceValue a) (sourceValue b)).symm
    change Standard.product a.value b.value _ = _
    rw [iha ha, ihb hb]
    delta Standard.product
    simpa [Expression.degree, sourceValue, Nat.cast_add] using h

end
end KIP126.Computation.Table
