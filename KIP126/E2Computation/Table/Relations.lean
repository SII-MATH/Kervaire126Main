module
import all KIP126.E2Computation.Table.Internal.ZeroDimension
public import KIP126.E2Computation.Table.Values
import all KIP126.E2Computation.Standard
/-! Primitive polynomial identities of the pinned source algebra,
LinProgram/Model/RelationCertificates.lean and Classes/Proofs.lean
at bbac1fc05843 (MIT), compared with the same actual sphere E₂.
These are original finite data identities, not the paper's AF13 conclusions. -/
namespace KIP126.Computation.Table
noncomputable section

/-- Original certificate at line 289. -/
public theorem h0_obstruction_rel0 :
    ((.mul (.named .h0) (.generator 24 5 36)) : Expression).value = 0 := by
  sorry

/-- Original certificate at line 304. -/
public theorem h0_obstruction_rel1 :
    ((.mul (.mul (.named .h0) (.generator 3 1 8)) (.generator 335 12 130)) : Expression).value = ((.mul (.mul (.named .h0) (.named .h0)) (.generator 425 12 137)) : Expression).value := by
  sorry

private theorem named_h0_obstruction_rel2_actual :
    ((.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_9_2)) : Expression).value = 0 := by
  have h2 := Standard.comparison_product 1 1 1 1 (by decide)
    (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)
  have h3 := Standard.comparison_product 2 2 1 1 (by decide)
    (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h2] at h3
  have h4 := Standard.comparison_product 3 3 1 1 (by decide)
    (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h3] at h4
  have h5 := Standard.comparison_product 4 4 1 1 (by decide)
    (Standard.sourceData.product 3 3 1 1 (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h4] at h5
  have h := Standard.comparison_product 5 5 9 134 (by decide)
    (Standard.sourceData.product 4 4 1 1 (Standard.sourceData.product 3 3 1 1 (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .x_125_9_2)
  rw [h5,Standard.namedSourceH02Zero,map_zero] at h
  exact h.symm

private theorem named_h0_obstruction_rel3_actual :
    ((.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)) : Expression).value = 0 := by
  have h2 := Standard.comparison_product 1 1 1 1 (by decide)
    (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)
  have h3 := Standard.comparison_product 2 2 1 1 (by decide)
    (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h2] at h3
  have h4 := Standard.comparison_product 3 3 1 1 (by decide)
    (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h3] at h4
  have h5 := Standard.comparison_product 4 4 1 1 (by decide)
    (Standard.sourceData.product 3 3 1 1 (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h4] at h5
  have h6 := Standard.comparison_product 5 5 1 1 (by decide)
    (Standard.sourceData.product 4 4 1 1 (Standard.sourceData.product 3 3 1 1 (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)
  rw [h5] at h6
  have h := Standard.comparison_product 6 6 8 133 (by decide)
    (Standard.sourceData.product 5 5 1 1 (Standard.sourceData.product 4 4 1 1 (Standard.sourceData.product 3 3 1 1 (Standard.sourceData.product 2 2 1 1 (Standard.sourceData.product 1 1 1 1 (Standard.sourceData.atom .h0) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .h0)) (Standard.sourceData.atom .x_125_8)
  rw [h6,Standard.namedSourceH03Zero,map_zero] at h
  exact h.symm


/-- Original certificate at line 326. -/
public theorem h0_obstruction_rel2 :
    ((.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_9_2)) : Expression).value = 0 := by
  exact named_h0_obstruction_rel2_actual

/-- Original certificate at line 341. -/
public theorem h0_obstruction_rel3 :
    ((.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)) : Expression).value = 0 := by
  exact named_h0_obstruction_rel3_actual

/-- Original certificate at line 433. -/
public theorem h2_obstruction_rel0 :
    ((.mul (.named .h2) (.generator 407 13 135)) : Expression).value = 0 := by
  sorry

/-- Original certificate at line 448. -/
public theorem h2_obstruction_rel1 :
    ((.mul (.named .h2) (.named .M_mul_d_0)) : Expression).value = ((.mul (.named .h0) (.generator 89 10 72)) : Expression).value := by
  sorry

/-- Original certificate at line 470. -/
public theorem h2_obstruction_rel2 :
    ((.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 89 10 72)) : Expression).value = 0 := by
  sorry

/-- Original certificate at line 108. -/
public theorem h1_h2_zero :
    ((.mul (.named .h1) (.named .h2)) : Expression).value = 0 := by
  exact Internal.actual_page_zero 2 6 (by decide) (by decide) _

end
end KIP126.Computation.Table
