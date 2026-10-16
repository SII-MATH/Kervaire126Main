module
import all KIP126.Computation.Table.Internal.ZeroDimension
public import KIP126.Computation.Table.Values
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

/-- Original certificate at line 326. -/
public theorem h0_obstruction_rel2 :
    ((.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_9_2)) : Expression).value = 0 := by
  sorry

/-- Original certificate at line 341. -/
public theorem h0_obstruction_rel3 :
    ((.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)) : Expression).value = 0 := by
  sorry

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
