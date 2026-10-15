module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Literature.Standard.Filtration
public import KIP126.Def.Computation.Table.Values
import all KIP126.Main.Internal.NuFifth.Frame
import all KIP126.Main.Internal.NuThree.Finite
import all KIP126.Main.Internal.FiniteReflection
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
/-! The complete original Q3-to-Q5 lift, NuFifth:2940–3016,3427–3498
at bbac1fc05843 (MIT). Main proves the finite gap, uniqueness, actual
product filtration and reflection through the same restriction map. -/
@[expose] section
namespace KIP126.Main.Internal.NuFifth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem nu_five_filtration_gap
    (a : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5)) :
    FiltrationAtLeast model.syntheticTower 10 a ↔ FiltrationAtLeast model.syntheticTower 11 a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 5 .sphere))
    10 11 125 134 (by decide)
  intro j hj hj'
  have : j=10 := by omega
  subst j
  exact finite_sphere_zero_of_classical_quotient 5 (by decide) 10 135 134 (by norm_num)
    nu_af10_cycle_quotient_zero

private theorem nu_three_x_detection_unique
    (x : model.classical.sphere.Page 2 (8,130))
    (a b : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3))
    (ha : FiniteDetected 3 (by decide) 8 130 0 x a)
    (hb : FiniteDetected 3 (by decide) 8 130 0 x b) : a=b := by
  apply sub_eq_zero.mp
  apply sphere_quotient_high_filtration_zero 3 (by decide) 122 130 11 (by decide)
  apply (NuThree.nu_three_x_gap (a-b)).mp
  exact detects_sub_filtration (model.convergence (.quotient 3 .sphere)) (8,130,130) ha.1 hb.1

theorem nu_five_of_three
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hnu : sphereFirstQuotient model 1 4 (quotientClass 1 nu)=KIP126.Computation.Standard.h2)
    (hthree : ∃ x : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3),
      ∃ y : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3),
      FiniteDetected 3 (by decide) 8 130 0 KIP126.Computation.Standard.X x ∧
      FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y y ∧ sphereAction nu x=y) :
    NuExtension5 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y nu := by
  obtain ⟨x3,y3,hx3,hy3,heq3⟩ := hthree
  obtain ⟨xr,hxr,hxn⟩ := KIP126.Computation.Standard.x_to_e6
  have hX : KIP126.Computation.Standard.X ∈ cycles model .sphere 5 (8,130) :=
    ((KIP126.ProofTools.isCycle_iff_reaches model .sphere 6 (by decide) (8,130) _).mpr ⟨xr,hxr⟩).2
  have hXn : KIP126.Computation.Standard.X≠0 := by
    intro h
    rw [h] at hxr
    exact hxn (FinitePageCalculus.represents_unique hxr (RepresentsOnPage.zero (by decide)))
  obtain ⟨x5,hx5⟩ := AlphaOne.finite_sphere_detection_exists 5 (by decide) 8 130 _ hX hXn
  let rho := (model.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 3 5 (by decide)
  have hxrho : x5≫rho=x3 := by
    apply nu_three_x_detection_unique _ _ _ _ hx3
    apply AlphaOne.finite_sphere_detected_rho 3 5 (by decide) (by decide) (by decide) 8 130 _ _ hXn x5 hx5
    exact cycles_antitone model .sphere (8,130) (by decide : (3:ℤ)≤5) hX
  have hnud := model.sphereDetectionCompatible.homotopy_lambda 1 4 0 nu
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient 1 4 (quotientClass 1 nu)=_ at hnu
  rw [hnu,lambda_zero_3_4] at hnud
  have hp : model.sphereAlgebra.product (1,4) (8,130)
      KIP126.Computation.Standard.h2 KIP126.Computation.Standard.X=0 := by
    have hc := KIP126.Computation.Table.product_comm 1 4 8 130 (by decide)
      KIP126.Computation.Standard.h2 KIP126.Computation.Standard.X
    have hz := hc.trans KIP126.Computation.Standard.x_h2_zero
    norm_num [KIP126.Computation.Standard.product,Category.id_comp] at hz ⊢
    exact hz
  have hy10 : FiltrationAtLeast model.syntheticTower 10
      (show BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5) from sphereAction nu x5) := by
    have hd := Standard.finite_action 5 (by decide) 1 4 8 130 0 0
      KIP126.Computation.Standard.h2 KIP126.Computation.Standard.X nu x5 hnud hx5.1
    change Detects (model.convergence (.quotient 5 .sphere)) (9,134,134)
      (quotientLabel 5 9 134 0 (model.sphereAlgebra.product (1,4) (8,130)
        KIP126.Computation.Standard.h2 KIP126.Computation.Standard.X)) (sphereAction nu x5) at hd
    rw [hp] at hd
    have hz : quotientLabel 5 9 134 0 (0 : model.classical.sphere.Page 2 (9,134))=0 := by
      simp only [quotientLabel,sphereLabel,map_zero]
    rw [hz] at hd
    exact detects_zero_filtration (model.convergence (.quotient 5 .sphere)) (9,134,134) hd
  have hy11 := (nu_five_filtration_gap (sphereAction nu x5)).mp hy10
  refine ⟨x5,sphereAction nu x5,hx5,?_,rfl⟩
  refine FiniteReflection.finite_sphere_detection_reflect 3 5 2 (by decide) (by decide) (by decide) 11 136
    KIP126.Computation.Standard.Y ?_ (sphereAction nu x5) hy11 ?_
  · obtain ⟨yr,hyr,_⟩ := KIP126.Computation.Standard.y_to_e5
    have hc := ((KIP126.ProofTools.isCycle_iff_reaches model .sphere 5 (by decide)
      (11,136) KIP126.Computation.Standard.Y).mpr ⟨yr,hyr⟩).2
    exact cycles_antitone model .sphere (11,136) (by decide : (3:ℤ)≤4) hc
  · have heq : sphereAction nu x5≫rho=y3 := by
      calc
        _ = sphereAction nu (x5≫rho) := by simp only [sphereAction,Category.assoc]
        _ = y3 := by rw [hxrho,heq3]
    change FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y (sphereAction nu x5≫rho)
    rw [heq]
    exact hy3

end
end KIP126.Main.Internal.NuFifth
