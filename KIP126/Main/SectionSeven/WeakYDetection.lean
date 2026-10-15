module
public import KIP126.Def.Computation.Table.Values
import all KIP126.Main.SectionSeven.WeakYFinite
import all KIP126.Main.SectionSeven.WeakInitialNonzero
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
/-! The final Y-detection argument of WeakYDetection.lean:987–1040,
2391–2497,2551–2569, bbac1fc05843 (MIT). Finite basis calculations are
proved in WeakYFinite; generic representatives reuse the shared Main operations. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.Algebra KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
open KIP126.Main.Internal.Selected.NuError
noncomputable section

private theorem weak_y_actual_af13_boundary :
    cycles model .sphere 3 (13,138) ≤ boundaries model .sphere 4 (13,138) := by
  intro x hx
  have hx' : Normalized.label (13,138) x ∈ nCycles 3 (13,138) := by
    change denormalize (13,138) (Normalized.label (13,138) x) ∈ cycles model .sphere 3 (13,138)
    rwa [denormalize_label]
  have h := WeakYFinite.af13_cycles_boundary hx'
  change denormalize (13,138) (Normalized.label (13,138) x) ∈ boundaries model .sphere 4 (13,138) at h
  rwa [denormalize_label] at h

private theorem weak_y_finite_cosets (x : model.classical.sphere.Page 2 (11,136))
    (hx : x∈cycles model .sphere 5 (11,136)) :
    x∈boundaries model .sphere 5 (11,136) ∨
    x-(show model.classical.sphere.Page 2 (11,136) from KIP126.Computation.Table.basis .sphere 11 136 3)
      ∈boundaries model .sphere 5 (11,136) := by
  have hx' : Normalized.label (11,136) x∈nCycles 5 (11,136) := by
    change denormalize (11,136) (Normalized.label (11,136) x)∈cycles model .sphere 5 (11,136)
    rwa [denormalize_label]
  rcases WeakYFinite.y_finite_cosets _ hx' with h|h
  · left
    change denormalize (11,136) (Normalized.label (11,136) x)∈boundaries model .sphere 5 (11,136) at h
    rwa [denormalize_label] at h
  · right
    change denormalize (11,136) (Normalized.label (11,136) x-Normalized.basis .sphere 11 136 3)
      ∈boundaries model .sphere 5 (11,136) at h
    rw [map_sub,denormalize_label] at h
    exact (denormalize_basis 11 136 3) ▸ h

private theorem weak_y_basis_label :
    KIP126.Computation.Table.basis .sphere 11 136 3 = KIP126.Computation.Standard.Y := by
  have h := KIP126.Computation.Table.basis_value
    ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_9_2),3⟩ (by decide)
  simpa only [KIP126.Computation.Table.Expression.value,KIP126.Computation.Table.Expression.degree,
    KIP126.Computation.Standard.Y,KIP126.Computation.Standard.h0Square,KIP126.Computation.Standard.atom_h0] using h

private theorem weak_y_filtration_twelve_fourteen
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    FiltrationAtLeast model.syntheticTower 12 a ↔ FiltrationAtLeast model.syntheticTower 14 a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 9 .sphere))
    12 14 125 132 (by decide)
  intro j hj hj'
  have hc : j=12 ∨ j=13 := by omega
  rcases hc with rfl|rfl
  · apply finite_sphere_zero_of_classical_quotient 9 (by decide) 12 137 132 (by decide)
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨x,rfl⟩ := Quotient.exists_rep x
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    exact boundaries_monotone model .sphere (12,137) (by decide : (3:ℤ)≤6)
      (nu9_af12_cycles_boundary (cycles_antitone model .sphere (12,137) (by decide : (2:ℤ)≤4) x.property))
  · apply finite_sphere_zero_of_classical_quotient 9 (by decide) 13 138 132 (by decide)
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨x,rfl⟩ := Quotient.exists_rep x
    exact (subquotientClass_eq_zero_iff _ _ _).mpr
      (boundaries_monotone model .sphere (13,138) (by decide : (4:ℤ)≤7)
        (weak_y_actual_af13_boundary x.property))

private theorem weak_y_infinity_label
    (e : ((model.family.quotient (S_0_0 : SyntheticSpectrum) 9).sequence.ssData (11,136,132)).eInfty)
    (hne : e≠0) : HasInfinityRepresentative (model.family.quotient (S_0_0 : SyntheticSpectrum) 9)
      2 (11,136,132) (quotientLabel 9 11 136 4 KIP126.Computation.Standard.Y) e := by
  obtain ⟨x,hx,he⟩ := finite_sphere_infinity_cycle_label_exists 9 4 (by decide) (by decide) 11 136 e
  have hn : x∉boundaries model .sphere 5 (11,136) := by
    intro hb
    have hz := finite_sphere_boundary_detects_zero 9 4 (by decide) (by decide) 11 136 x hb
    exact nonzero_detection_ne_zero (.quotient 9 .sphere) (11,136,132)
      (quotientLabel 9 11 136 4 x) 0 ⟨hz,e,he,hne⟩ rfl
  have hb := (weak_y_finite_cosets x hx).resolve_left hn
  rw [weak_y_basis_label] at hb
  have hy : KIP126.Computation.Standard.Y∈cycles model .sphere 5 (11,136) := by
    have hh := (cycles model .sphere 5 (11,136)).sub_mem hx
      (boundaries_le_cycles model .sphere (11,136) 5 5 hb)
    simpa only [sub_sub_cancel] using hh
  let y : cycles model .sphere 5 (11,136) := ⟨KIP126.Computation.Standard.Y,hy⟩
  apply (finite_sphere_frame 9 4 (by decide) (by decide) 11 136 y ?_ e).resolve_left hne
  intro q
  obtain ⟨c,rfl⟩ := Quotient.exists_rep q
  rcases weak_y_finite_cosets c.val c.property with hc|hc
  · exact Or.inl ((subquotientClass_eq_zero_iff _ _ _).mpr hc)
  · right
    apply sub_eq_zero.mp
    change subquotientClass (cycles model .sphere 5 (11,136)) (boundaries model .sphere 5 (11,136)) c -
      subquotientClass (cycles model .sphere 5 (11,136)) (boundaries model .sphere 5 (11,136)) y = 0
    rw [←map_sub]
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change (show model.classical.sphere.Page 2 (11,136) from c.val)-KIP126.Computation.Standard.Y∈boundaries model .sphere 5 (11,136)
    rwa [weak_y_basis_label] at hc

private theorem weak_y_detected_of_filtration_bounds
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (h11 : FiltrationAtLeast model.syntheticTower 11 z)
    (h12 : ¬FiltrationAtLeast model.syntheticTower 12 z) :
    FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y z := by
  obtain ⟨x,_,hx⟩ := finite_sphere_filtration_has_cycle_label 9 4 (by decide) (by decide) 11 136 z h11
  obtain ⟨e,he,a,ha,hgr⟩ := hx
  have hn : e≠0 := by
    intro hz
    apply h12
    exact detects_zero_infinity_filtration (model.convergence (.quotient 9 .sphere)) (11,136,132)
      ⟨e,he,a,ha,hgr⟩ (hz ▸ he)
  have hy := weak_y_infinity_label e hn
  exact ⟨⟨e,hy,a,ha,hgr⟩,e,hy,hn⟩

theorem weak_y_detected_of_f11_and_nonzero
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hd : Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 KIP126.Computation.Standard.h0) h0)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hf11 : FiltrationAtLeast model.syntheticTower 11 y0)
    (hne : lambdaMultiply 2 (sphereAction h0 y0)≠0) :
    FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y y0 := by
  apply weak_y_detected_of_filtration_bounds y0 hf11
  intro hf12
  have hf14 := (weak_y_filtration_twelve_fourteen y0).mp hf12
  have hf15 := KIP126.Literature.Standard.action_filtration (.quotient 9 .sphere)
    0 1 125 132 1 14 h0 y0 (detected_filtration .sphere (1,1,1) hd) hf14
  have hf := lambda_filtration_preserved 2 15 (sphereAction h0 y0) hf15
  exact hne (sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide)
    (lambdaMultiply 2 (sphereAction h0 y0)) hf)

end
end KIP126.Main.SectionSeven.Internal
