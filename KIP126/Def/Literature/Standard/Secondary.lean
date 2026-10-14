module

public import KIP126.Def.Literature.Standard

/-! The two source-to-synthetic secondary-operation comparisons previously
left unfinished in Kervaire126 bbac1fc05843,
Main/Solution/StageInput.lean:281 and :289 (MIT; see the retained source LICENSE).
They are upstream Literature responsibilities, not proof obligations of the
paper's Main module. The second comparison retains the actual order-two
hypothesis for every theta, not just the selected theta_5. -/

@[expose] section
namespace KIP126.Literature.Standard
open KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Standard (SyntheticSpectrum)
noncomputable section

/-- Low Toda comparison used at MainPaper/main.tex:2498.
This is the original pending secondary-operation comparison. -/
public theorem toda_eta_squared :
    Route.TripleToda syntheticH0 eta syntheticH0
      (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) eta eta) := by
  sorry

/-- The symmetric comparison retains the synthetic λ² normalization from
MainPaper/main.tex:2550-2551 and applies to each actual order-two theta. -/
public theorem toda_symmetric
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : theta + theta = 0) :
    Route.TripleToda Route.syntheticTwo theta Route.syntheticTwo
      (lambdaMultiply 2 (sphereProduct eta theta)) := by
  sorry

end
end KIP126.Literature.Standard
