module
public import KIP126.Main.Conditions
public import KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.Main.Internal.Choice.LambdaInjectivity

/-! The original realization-injectivity proof of exponent two in degree (62,64),
Selected/ChoiceInvariance:686–741, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem no_outgoing_stem63_nonpositive (q : ℤ) (hq : q ≤ 0) :
    NoOutgoingAt model.classical.sphere q (q+63) := by
  intro r _ x
  have hzero : Subsingleton (model.classical.sphere.Page r (q,q+63)) := by
    by_cases hq0 : q=0
    · subst q
      exact KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero r 63 (by decide)
    · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q (q+63) (by omega)
  rw [hzero.elim x 0,map_zero]

private theorem realization_additive : model.recovery.realization.Additive := by
  letI := model.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts model.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem realization_injective_of_lambda_powers
    (X : SyntheticObject) (m wt : ℤ)
    (h : LambdaPowersInjectiveAt m wt (X.obj model.nu model.auxiliary)) :
    Function.Injective (fun a : BiHom m wt (X.obj model.nu model.auxiliary) =>
      model.recovery.realization.map a) := by
  letI := realization_additive
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨k,hk⟩ := (KIP126.Literature.Standard.selected_realization_kernel X m wt (a-b)).mp
    (by simp only [Functor.map_sub,hab,sub_self])
  apply h k
  simpa only [lambdaMultiply,Category.comp_id,Category.assoc,Limits.comp_zero] using hk

private theorem theta_degree_order_two (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    theta+theta=0 := by
  classical
  have hnu : LambdaPowersInjectiveAt 62 64 (model.nu.functor.obj SphereSpectrum) := by
    apply nu_lambda_powers_injective_of_source_halfplane .sphere 62 64
    intro q hq
    simpa only [ClassicalObject.obj,add_assoc,show (62:ℤ)+1=63 by norm_num] using
      no_outgoing_stem63_nonpositive q (by omega)
  have hsphere : LambdaPowersInjectiveAt 62 64 (S_0_0 : SyntheticSpectrum) := by
    intro n a b hab
    apply (cancel_mono model.nu.unitIso.inv).mp
    apply hnu n
    simpa only [lambdaMultiply,Category.assoc] using
      congrArg (fun z=>z ≫ model.nu.unitIso.inv) hab
  have hinj := realization_injective_of_lambda_powers
    .sphere 62 64 hsphere
  letI := model.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts model.recovery.realization
  letI : model.recovery.realization.Additive := Functor.additive_of_preservesBinaryBiproducts _
  apply hinj
  simp only [Functor.map_add,Functor.map_zero]
  let α : HomotopyGroup (C:=Spectrum) 62 SphereSpectrum :=
    (KIP126.Literature.Standard.realization_sphere 62 64).hom ≫ model.recovery.realization.map theta ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
  have h := KIP126.Literature.Standard.stem62_exponent_two α
  apply (cancel_epi (KIP126.Literature.Standard.realization_sphere 62 64).hom).mp
  apply (cancel_mono (model.recovery.realization.map model.nu.unitIso.inv)).mp
  apply (cancel_mono ((model.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
  erw [Preadditive.comp_add,Preadditive.add_comp,Preadditive.add_comp,
    Limits.comp_zero,Limits.zero_comp,Limits.zero_comp]
  repeat erw [Category.assoc]
  exact h


end
end KIP126.Main.Internal.Choice
end
