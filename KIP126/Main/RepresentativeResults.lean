module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.ProductDetection
import all KIP126.Main.Internal.Selected.ProductZero
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! Actual representatives on the fixed sphere. The existence and filtration
arguments are the migrated proofs from bbac1fc05843
Main/Solution/Route/Selected/DetectionData.lean (MIT). The exact lambda-six
equation follows from that filtration bound and the existing BHS comparison;
it makes no additional assertion about the leading detection of its lift. -/

@[expose] section
namespace KIP126.Main
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual nonzero permanent class U has a representative on the sphere. -/
public theorem u_choice_exists :
    ∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u := by
  exact Internal.Selected.u_choice_exists

/-- Every U representative has its lambda-three eta product in filtration 14. -/
public theorem lambda_three_eta_u_filtration_fourteen
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    FiltrationAtLeast model.syntheticTower 14
      (lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) := by
  exact Internal.Selected.u_choice_eta_lambda_three_filtration_fourteen
    Internal.Selected.h1_u_zero u hu

/-- Actual lambda-six divisibility, retaining the choice of lift. A specified
T detection of that lift is not a premise or a conclusion of this equation. -/
public theorem lambda_three_eta_u_eq_lambda_six
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    ∃ y : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u) =
        lambdaMultiply 6 y := by
  let a : BiHom 125 133 (S_0_0 : SyntheticSpectrum) :=
    lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)
  have ha : FiltrationAtLeast model.syntheticTower 14 a :=
    lambda_three_eta_u_filtration_fourteen u hu
  have h := KIP126.Literature.Standard.selected_filtration_lambda
    .sphere 125 133 14 (by decide) (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 14 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 139 (model.nu.functor.obj SphereSpectrum),
      lambdaMultiply 6 b = a ≫ model.nu.unitIso.inv at h
  obtain ⟨b, hb⟩ := h.mp
    (Internal.Selected.map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha)
  refine ⟨b ≫ model.nu.unitIso.hom, ?_⟩
  symm
  simpa only [a, lambdaMultiply, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun z => z ≫ model.nu.unitIso.hom) hb

/-- The difference of two lambda-three eta products lies in filtration 14
at degree (125, 133). The stronger filtration-15 bound remains a separate goal. -/
public theorem lambda_three_eta_u_difference_filtration_fourteen
    (u u' : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hu : UChoice u) (hu' : UChoice u') :
    FiltrationAtLeast model.syntheticTower 14
      ((show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from
          lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) -
        (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from
          lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u'))) := by
  exact (model.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum)
    14 (125, 133)).sub_mem
      (lambda_three_eta_u_filtration_fourteen u hu)
      (lambda_three_eta_u_filtration_fourteen u' hu')

end
end KIP126.Main
