module
public import KIP126.Main.Conditions
public import KIP126.Literature.Standard.QuotientAlgebra
public import KIP126.Literature.Standard.Filtration
public import KIP126.Computation.Table.Values
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.Choice.OrderTwo
import all KIP126.Main.Internal.Theta.OrderTwo
import all KIP126.Main.Internal.Theta.Shuffle
import all KIP126.Main.Internal.LowEta

/-! Original bracket existence, ThetaToda.lean:1023–1058,
and fixed shuffle wrapper, ThetaShuffle.lean:637–653, bbac1fc05843 (MIT). The entire cofiber argument is retained. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Toda
open KIP126.Core.SpectralSequence KIP126.Core.Algebra
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
open KIP126.Literature.Standard (quotientSyntheticSymmetric quotientAlgebra quotientAlgebraProduct quotientAlgebra_commutative quotientAlgebra_unit quotientAlgebra_sphere_action quotientAlgebra_first_quotient)
open KIP126.Computation.Standard (product h0 h6 h5Square atom_h0 atom_h5 atom_h6)
open KIP126.Computation.Table
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive := model.exactness.shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem synthetic_theta_b_bracket_nonempty
    (coh : BiShiftCoherence SyntheticSpectrum)
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (htheta : theta+theta=0) (hb : b+b=0) :
    ∃ z : BiHom 125 134 (S_0_0 : SyntheticSpectrum), TripleToda theta syntheticTwo b z := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (62,70)
  let f := F.map theta
  let g := (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0:SyntheticSpectrum) ≫ F.map syntheticTwo
  have hg : g=2 • 𝟙 (Smn 62 70 : SyntheticSpectrum) := by
    have hc := coh.left_unit (62,70) (S_0_0:SyntheticSpectrum)
    change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _=_ at hc
    have he : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0:SyntheticSpectrum)=
        F.map (SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,F] using hc
    dsimp only [g,syntheticTwo]
    rw [Functor.map_comp,←he,←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    simp only [Functor.map_nsmul]
    change 2 • F.map (𝟙 (S_0_0 : SyntheticSpectrum)) = 2 • 𝟙 (F.obj (S_0_0 : SyntheticSpectrum))
    rw [CategoryTheory.Functor.map_id]
  have hfg : f≫g=0 := by
    rw [hg]
    simp only [two_smul,Preadditive.comp_add]
    erw [Category.comp_id]
    change F.map theta+F.map theta=0
    rw [←Functor.map_add,htheta,Functor.map_zero]
  have hgb : g≫b=0 := by
    rw [hg]
    simp only [two_smul,Preadditive.add_comp]
    erw [Category.id_comp]
    exact hb
  obtain ⟨v,hv⟩ := Toda.exists_relation f g b hfg hgb
  refine ⟨(tripleTodaSource 62 64 0 0 62 70).hom≫v,?_⟩
  unfold TripleToda
  rw [Iso.inv_hom_id_assoc]
  exact hv

private theorem tripleToda_right_order_two
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (z : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hz : TripleToda theta syntheticTwo b z) : b+b=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (62,70)
  let g := (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0:SyntheticSpectrum) ≫ F.map syntheticTwo
  have hg : g=2 • 𝟙 (Smn 62 70 : SyntheticSpectrum) := by
    have hc := model.quotients.coherence.left_unit (62,70) (S_0_0:SyntheticSpectrum)
    change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _=_ at hc
    have he : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0:SyntheticSpectrum)=
        F.map (SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,F] using hc
    dsimp only [g,syntheticTwo]
    rw [Functor.map_comp,←he,←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    simp only [Functor.map_nsmul]
    change 2 • F.map (𝟙 (S_0_0 : SyntheticSpectrum)) = 2 • 𝟙 (F.obj (S_0_0 : SyntheticSpectrum))
    rw [CategoryTheory.Functor.map_id]
  have hb := (Toda.composable hz).2
  change g ≫ b=0 at hb
  rw [hg] at hb
  simp only [two_smul,Preadditive.add_comp] at hb
  erw [Category.id_comp] at hb
  exact hb

private theorem theta_b_multiplied_shuffle
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta)
    (htheta2 : theta+theta=0)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (z : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hz : TripleToda theta syntheticTwo b z) :
    quotientClass 9 (lambdaMultiply 2 (sphereProduct KIP126.Literature.Standard.syntheticH0 z)) =
      quotientClass 9 (lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta (sphereProduct theta b))) := by
  exact theta_b_shuffle_from_low_degrees
    KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.eta
    KIP126.Literature.Standard.toda_lambda_h0 theta b htheta2
    (tripleToda_right_order_two theta b z hz) z hz
    (KIP126.Literature.Standard.toda_symmetric theta htheta2)

end
end KIP126.Main.Internal.Theta
