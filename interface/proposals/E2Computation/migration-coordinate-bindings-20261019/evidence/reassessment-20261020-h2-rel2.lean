module
import all KIP126.E2Computation.Table.Relations
import all KIP126.E2Computation.Table.Internal.SourceExpression
import all KIP126.E2Computation.Table.Internal.H2Annihilation
namespace KIP126.Computation.Table
open Standard Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
private theorem h2_rel2_from_registered_rel1 :
    ((.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 89 10 72)) : Expression).value = 0 := by
  have h := h2_obstruction_rel1
  rw [value_comparison _ (by decide), value_comparison _ (by decide)] at h
  have hs := (comparison 11 73 (by decide)).injective h
  have hv := congrArg Subtype.val hs
  let g := (sourceValue (.generator 89 10 72)).val
  change h2X ⟨2,by decide⟩ * h2X ⟨79,by decide⟩ = h2X ⟨0,by decide⟩ * g at hv
  have hz : h2X ⟨0,by decide⟩ ^ 3 * g = 0 := by
    calc
      _ = h2X ⟨0,by decide⟩ ^ 2 * (h2X ⟨2,by decide⟩ * h2X ⟨79,by decide⟩) := by rw [hv]; ring
      _ = -(h2X ⟨1,by decide⟩ ^ 3) * h2X ⟨79,by decide⟩ := by
        have he := eq_neg_of_add_eq_zero_right h2Relation2
        calc
          _ = (h2X ⟨0,by decide⟩ ^ 2 * h2X ⟨2,by decide⟩) * h2X ⟨79,by decide⟩ := by ring
          _ = _ := by rw [he]
      _ = -(h2X ⟨1,by decide⟩ * (h2X ⟨1,by decide⟩ ^ 2 * h2X ⟨79,by decide⟩)) := by ring
      _ = 0 := by rw [h2Relation859]; simp
  rw [value_comparison _ (by decide)]
  apply (comparison 13 75 (by decide)).map_eq_zero_iff.mpr
  apply Subtype.ext
  change (h2X ⟨0,by decide⟩ * h2X ⟨0,by decide⟩) * h2X ⟨0,by decide⟩ * g = 0
  simpa only [pow_succ,pow_zero,mul_one,one_mul] using hz
end
end KIP126.Computation.Table

#print axioms KIP126.Computation.Table.h2_rel2_from_registered_rel1
