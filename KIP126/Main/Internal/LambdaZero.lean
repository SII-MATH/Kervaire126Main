module
public import KIP126.Main.Conditions
/-! Right unit calculations used in NuTargetHelpers.lean:1644–1671
(bbac1fc05843, MIT). -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace KIP126.Main.Internal
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic.Standard
noncomputable section
theorem lambda_zero_3_4 (a : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (3,4) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 3 4 : SyntheticSpectrum) := by
    change (biShiftAddIso (3,4) (0,0) (3,4) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (3,4) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]


theorem lambda_zero_125_139 (a : BiHom 125 139 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (125,139) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 125 139 : SyntheticSpectrum) := by
    change (biShiftAddIso (125,139) (0,0) (125,139) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (125,139) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

end
end KIP126.Main.Internal
