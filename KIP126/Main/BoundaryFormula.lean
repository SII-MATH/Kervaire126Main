module

public import KIP126.Main.Conditions

import all KIP126.Main.ChoiceIndependence
/-! The connecting-map formula on the actual first-quotient h6 square.
The fixed BX choice is supplied by Literature. Passing to another detected
theta uses the separately registered Main choice-independence obligation. -/

@[expose] section
namespace KIP126.Main
open KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section

/-- The connecting map is applied to the actual first-quotient class whose
comparison is the standard h6 square, at the fixed BX choice. -/
private theorem delta_h6_square_bx :
    KIP126.Literature.deltaH6Square model =
      KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5 := by
  exact KIP126.Literature.Standard.bx_total_boundary

/-- The same actual boundary formula at any admissible theta. Its remaining
Main dependency is `lambda_eta_theta_square_independent`. -/
public theorem delta_h6_square_eq_lambda_eta_theta_square
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.deltaH6Square model =
      KIP126.Literature.Standard.lambdaEtaThetaSquare theta := by
  exact delta_h6_square_bx.trans
    (lambda_eta_theta_square_independent theta htheta).symm

end
end KIP126.Main
