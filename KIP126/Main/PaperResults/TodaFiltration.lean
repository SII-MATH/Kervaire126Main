module

import all KIP126.Main.Internal.AlphaOne.FiniteWindow
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.SectionSeven.WeakStrip
import all KIP126.Main.SectionSeven.NuTargetFiniteGap

/-! Finite-quotient bounds on the actual right indeterminacy of the
alpha-one Toda bracket. These are auxiliary bounds, not a claim that a
filtered Toda member has already been constructed. -/

@[expose] section
namespace KIP126.Main.Paper.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.ProofTools.Operations
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem stem124_low_finite_quotient_zero
    (s r : ℤ) (hs : 6 ≤ s ∧ s ≤ 9) (hr : 2 ≤ r) (hrc : r ≤ 16-s)
    (hz : Subsingleton (Normalized.sphere.Page r (s,s+124))) :
    Subsingleton (KIP126.Literature.CycleQuotient model .sphere (15-s) (s-5) (s,s+124)) := by
  apply AlphaOne.quotient_vanishing_actual
  apply AlphaOne.quotient_subsingleton_of_le
  intro x hx
  obtain ⟨_,hxc⟩ := (AlphaOne.cycles_reaches (15-s) (s,s+124) (by omega) x).mp hx
  obtain ⟨xr,hxr⟩ := represents_before hr (show r ≤ 15-s+1 by omega) hxc
  rw [hz.elim xr 0] at hxr
  have hb := AlphaOne.stem123_weight130_finite_quotients_boundary_of_zero_representative hxr
  let E := Normalized.sphere
  let A := E.ssData (s,s+124)
  have hin (m : ℤ) (hm : s-4 ≤ m) : E.d m ((s,s+124)-E.diffDeg m)=0 := by
    have hi : (s,s+124)-E.diffDeg m=(s-m,(s-m)+125) := by
      change (s,s+124)-(m,m-1)=_
      ext <;> dsimp <;> omega
    rw [hi]
    ext z
    exact no_outgoing_stem125_low (s-m) (by omega) m (by omega) z
  have hB := boundaries_top_eq_of_d_eq_zero E (s-4) (by change (2:ℤ)≤s-4; omega) (s,s+124) hin
  change A.B ⊤=A.B ↑(s-4-2).toNat at hB
  have hle : A.B ↑(r-1-1).toNat ≤ A.B ↑(s-5-1).toNat := by
    have hi : s-4-2=s-5-1 := by omega
    rw [hi] at hB
    exact (A.B_mono le_top).trans hB.le
  obtain ⟨y,hy⟩ := hb
  refine ⟨(Subobject.ofLE _ _ hle) y,?_⟩
  change (Subobject.ofLE _ _ hle ≫ AlphaOne.boundaryMap (↑(s-5-1).toNat) (s,s+124)) y=x
  simpa only [AlphaOne.boundaryMap,AlphaOne.boundaryMapFor,A,E,
    ←Category.assoc,Subobject.ofLE_comp_ofLE] using hy

private theorem ninth_stem124_weight130_filtration_ten
    (a : BiHom 124 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    FiltrationAtLeast model.syntheticTower 10 a := by
  have h6 := finite_sphere_bottom_filtration 9 (by decide) 6 130 a
  apply (filtration_iff_of_infinity_zero (model.convergence (.quotient 9 .sphere))
    6 10 124 130 (by decide) ?_ a).mp h6
  intro s hs hs'
  have hss : 6 ≤ s ∧ s ≤ 9 := by omega
  have hz : Subsingleton (KIP126.Literature.CycleQuotient model .sphere (15-s) (s-5) (s,s+124)) := by
    obtain ⟨h6,h7,h8,h9⟩ := stem124_finite_pages
    interval_cases s
    · exact stem124_low_finite_quotient_zero 6 6 (by decide) (by decide) (by decide) h6
    · exact stem124_low_finite_quotient_zero 7 6 (by decide) (by decide) (by decide) h7
    · exact stem124_low_finite_quotient_zero 8 3 (by decide) (by decide) (by decide) h8
    · exact stem124_low_finite_quotient_zero 9 4 (by decide) (by decide) (by decide) h9
  rw [show 124+s=s+124 by omega]
  apply finite_sphere_zero_of_classical_quotient 9 (by decide) s (s+124) 130 (by constructor <;> omega)
  convert hz using 1 <;> congr 1 <;> norm_num <;> omega

private theorem eta_ninth_stem124_weight130_filtration_eleven
    (a : BiHom 124 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    FiltrationAtLeast model.syntheticTower 11
      (sphereAction KIP126.Literature.Standard.eta a) := by
  have heta := model.sphereDetectionCompatible.homotopy_lambda 1 2 0 KIP126.Literature.Standard.eta
  change Detects (model.convergence .sphere) (1,2,2)
    (sphereLabel 1 2 0 (KIP126.Literature.sphereFirstQuotient model 1 2
      (quotientClass 1 KIP126.Literature.Standard.eta)))
    (lambdaMultiply 0 KIP126.Literature.Standard.eta) at heta
  rw [KIP126.Literature.Standard.eta_label,lambda_zero_1_2] at heta
  exact KIP126.Literature.Standard.action_filtration (.quotient 9 .sphere)
    1 2 124 130 1 10 KIP126.Literature.Standard.eta a
    (detected_filtration .sphere (1,2,2) heta)
    (ninth_stem124_weight130_filtration_ten a)

end
end KIP126.Main.Paper.Internal
