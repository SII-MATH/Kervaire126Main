module
public import KIP126.Main.Conditions
public import KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.Main.Internal.Choice.LambdaInjectivity

/-! Classical low-filtration support and additivity of realization. Choice transport uses the
selected BX representative's sourced order-two property; it does not require
an exponent-two assertion for every integral synthetic representative. -/
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

end
end KIP126.Main.Internal.Choice
end
