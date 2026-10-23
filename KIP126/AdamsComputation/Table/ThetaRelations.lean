module
import all KIP126.AdamsComputation.Table.Internal.ZeroDimension
import all KIP126.AdamsComputation.Table.Internal.ThetaAnnihilation
public import KIP126.AdamsComputation.Table.Values

/-! Exact primitive equations of the pinned finite algebra (bbac1fc05843, MIT).
These were checked in LinProgram/Certificates/Relations/ThetaMassey.
These equations use the existing archive-to-actual-E₂ comparison. The paper's
finite-span and Massey-indeterminacy arguments remain in Main. -/
namespace KIP126.Computation.Table
noncomputable section

private theorem thetaActualZero
    (id : ℕ) :
    ((.mul (.named .h5) (.generator id 7 70)) : Expression).value = 0 := by
  let x := (Standard.comparison 7 70 (by decide)).symm (generatorImage id 7 70)
  have h := Standard.comparison_product 1 32 7 70 (by decide)
    (Standard.sourceData.atom .h5) x
  rw [Internal.thetaSourceZero,map_zero] at h
  have hx : Standard.comparison 7 70 (by decide) x = generatorImage id 7 70 :=
    (Standard.comparison 7 70 (by decide)).apply_symm_apply _
  rw [hx] at h
  exact h.symm

/-- Original raw relation `18,1,85,1`. -/
public theorem theta_h5_generator85_zero :
    ((.mul (.named .h5) (.generator 85 7 70)) : Expression).value = 0 := by
  exact thetaActualZero _

/-- Original raw relation `18,1,84,1`. -/
public theorem theta_h5_generator84_zero :
    ((.mul (.named .h5) (.generator 84 7 70)) : Expression).value = 0 := by
  exact thetaActualZero _

/-- Original raw relation `18,1,69,1`. -/
public theorem theta_h5_h6_zero :
    ((.mul (.named .h5) (.named .h6)) : Expression).value = 0 := by
  exact Internal.actual_page_zero 2 96 (by decide) (by decide) _

end
end KIP126.Computation.Table
