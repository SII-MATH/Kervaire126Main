module
public import KIP126.Main.Conditions
public import KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.High125.Finite
import all KIP126.Main.Internal.High125.Tail
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Choice.Filtration
/-! Original high125 filtration argument, Main/Solution/Computation/High125
and Route/CofiberAndFiltration, bbac1fc05843 (MIT). Finite calculations are
transported back to the fixed actual sphere. Infinite tails use the sourced
vanishing line and the existing separation/boundedness interfaces. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature KIP126.Main.Internal.Selected KIP126.Main.Internal.Choice
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem stem125_page_five_tail (s : ℤ) (hs : 26 ≤ s) :
    Subsingleton (model.classical.sphere.Page 5 (s,125+s)) := by
  by_cases h64 : s ≤ 64
  · have h := stem125_e5_zero_finite s.toNat (by omega) (by omega)
    rw [Normalized.sequence_eq] at h
    simpa only [KIP126.Computation.Table.sequence,KIP126.Computation.Table.object,
      Int.toNat_of_nonneg (by omega : 0≤s),add_comm] using h
  · apply page_subsingleton_of_le model.classical.sphere 2 5 s (125+s) (by decide) (by decide)
    exact Standard.sphereVanishing s (125+s) (by omega) (by omega)

private theorem stem125_page_six_middle (s : ℤ) (hs : 15 ≤ s) (hs' : s < 25) :
    Subsingleton (model.classical.sphere.Page 6 (s,125+s)) := by
  have h : Subsingleton (Normalized.sphere.Page 6 (s.toNat,(s.toNat:ℤ)+125)) := by
    by_cases h20 : s < 20
    · exact stem125_sixth_pages_15_19 s.toNat (by omega) (by omega)
    · exact stem125_sixth_pages_20_24 s.toNat (by omega) (by omega)
  change Subsingleton ((Normalized.sequence .sphere).Page 6 _) at h
  rw [Normalized.sequence_eq] at h
  simpa only [KIP126.Computation.Table.sequence,KIP126.Computation.Table.object,
    Int.toNat_of_nonneg (by omega : 0≤s),add_comm] using h

private theorem synthetic_tail_grade_zero (s : ℤ) (hs : 26 ≤ s) :
    IsZero (model.family.sphere.sequence.ssData (s,125+s,130)).eInfty := by
  apply sphere_infinity_zero_of_permanent_quotient_zero s (125+s) 130 (by omega)
  exact permanent_quotient_zero_of_page_zero .sphere 5 _ (by decide) (by omega)
    (s,125+s) (stem125_page_five_tail s hs)

private theorem synthetic_middle_grade_zero (s : ℤ) (hs : 15 ≤ s) (hs' : s < 25) :
    IsZero (model.family.sphere.sequence.ssData (s,125+s,130)).eInfty := by
  apply sphere_infinity_zero_of_permanent_quotient_zero s (125+s) 130 (by omega)
  exact permanent_quotient_zero_of_page_zero .sphere 6 _ (by decide) (by omega)
    (s,125+s) (stem125_page_six_middle s hs hs')

theorem synthetic_filtration_fifteen_to_twentyfive
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 15 a) :
    FiltrationAtLeast model.syntheticTower 25 a := by
  have step (s : ℕ) (hs : 15≤s) (hs' : s<25)
      (h : FiltrationAtLeast model.syntheticTower s a) :
      FiltrationAtLeast model.syntheticTower (s+1) a :=
    filtration_step_of_infinity_zero (model.convergence .sphere) s 125 130
      (synthetic_middle_grade_zero s (by omega) (by omega)) a h
  have all (s : ℕ) (hs : 15≤s) (hs' : s≤25) : FiltrationAtLeast model.syntheticTower s a := by
    induction s,hs using Nat.le_induction with
    | base => exact ha
    | succ n hn ih => exact_mod_cast step n hn (by omega) (ih (by omega))
  exact all 25 (by decide) (by decide)

theorem synthetic_filtration26_zero (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 26 a) : a=0 := by
  apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated .sphere 125 130 a
  intro s
  by_cases hs : s≤26
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (125,130) (by omega) ha
  · have all (s : ℕ) (hs : 26≤s) : FiltrationAtLeast model.syntheticTower s a := by
      induction s,hs using Nat.le_induction with
      | base => exact ha
      | succ n hn ih =>
        have h := filtration_step_of_infinity_zero (model.convergence .sphere) n 125 130
          (synthetic_tail_grade_zero n (by omega)) a ih
        simpa only [Nat.cast_add,Nat.cast_one] using h
    exact all s (by omega)

private theorem classical_tail_grade_zero (s : ℤ) (hs : 26≤s) :
    Subsingleton (model.classical.sphere.ssData (s,125+s)).eInfty := by
  let P := model.classical.sphere.ssData (s,125+s)
  let n : WithTop ℕ := ↑(5-model.classical.sphere.r₀).toNat
  have hp : Subsingleton (P.page n) := stem125_page_five_tail s hs
  have hall (e : P.eInfty) : e=0 := by
    haveI : Epi (P.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (P.pageπ ⊤)).mp inferInstance e
    have h := P.infinity_projection_eq_of_page_projection_eq n z 0 (hp.elim _ _)
    simpa only [map_zero] using h
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem classical_filtration_step (s : ℤ) (hs : 26≤s)
    (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 125) :
    a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule (s+1) 125 := by
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  haveI := classical_tail_grade_zero s hs
  have e : (model.classical.sphere.ssData (s,125+s)).eInfty ≅ F.associatedGraded s 125 := by
    simpa only [add_sub_cancel_right,F,ClassicalObject.obj,ClassicalAdamsFamily.sphere] using (model.classicalConvergence .sphere).identification (s,125+s)
  haveI : Subsingleton (F.associatedGraded s 125) := (ModuleCat.mono_iff_injective e.inv).mp inferInstance |>.subsingleton
  have hm : a ∈ (ModuleCat.subobjectModule _) (F.F s 125) := by
    simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  obtain ⟨b,hb⟩ := hm
  have hz : F.toAssociatedGraded s 125 b=0 := Subsingleton.elim _ _
  have hn := (F.toAssociatedGraded_eq_zero_iff s 125 b).mp hz
  rw [hb] at hn
  simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hn

theorem classical_filtration26_zero (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 26 125) : a=0 := by
  have all (s : ℕ) (hs : 26≤s) :
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 125 := by
    induction s,hs using Nat.le_induction with
    | base => exact ha
    | succ k hk ih =>
      simpa only [Nat.cast_add,Nat.cast_one] using classical_filtration_step k (by omega) a ih
  apply KIP126.AdamsSynthetic.Standard.classical_sphere_separated 125 a
  intro s
  by_cases hs : s≤26
  · exact (model.classicalTower.tower SphereSpectrum).filtrationSubmodule_antitone 125 (by omega) ha
  · exact all s (by omega)


end
end KIP126.Main.Internal.High125
