module
public import KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! The h₀–ν commutation steps of NuTargetHelpers.lean:2569–2731,
bbac1fc05843 (MIT). The first equality follows directly from the existing
actual graded-commutativity interface; the action associativity proof is retained. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal
noncomputable section
theorem h0_nu_commute
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) :
    sphereAction h0 nu = sphereAction nu h0 := by
  have h := model.sphereProductCommutative 0 1 3 4 h0 nu
  simpa only [Int.zero_mul,Int.natAbs_zero,pow_zero,one_smul,homotopyRegrade,sphereProduct,sphereAction] using h

theorem h0_nu_actions_commute {X : SyntheticSpectrum}
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (ν : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (x : BiHom 122 126 X) :
    sphereAction h0 (sphereAction ν x)=sphereAction ν (sphereAction h0 x) := by
  have hleft : sphereAction (sphereAction h0 ν) x=sphereAction h0 (sphereAction ν x) := by
    have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (0,1) (3,4) (122,126)
      (3,5) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at ha
    unfold sphereAction
    simp only [Functor.map_comp,Category.assoc]
    erw [reassoc_of% ((SyntheticCategory.biShift_comp (3,4) (122,126)).inv.naturality h0)]
    erw [← reassoc_of% ha]
    rfl
  have hright : sphereAction (sphereAction ν h0) x=sphereAction ν (sphereAction h0 x) := by
    have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (3,4) (0,1) (122,126)
      (3,5) (122,127) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at ha
    unfold sphereAction
    simp only [Functor.map_comp,Category.assoc]
    erw [reassoc_of% ((SyntheticCategory.biShift_comp (0,1) (122,126)).inv.naturality ν)]
    erw [← reassoc_of% ha]
    rfl
  rw [←hleft,←hright,h0_nu_commute h0 ν]
end
end KIP126.Main.SectionSeven.Internal
