module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.CofiberCoordinates
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Stem125Vanishing

/-! The filtration-separation and detection-uniqueness arguments in Section 7. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
/-- The classical F26 vanishing needed to remove the indeterminacy of BMQ's
high125 detector.  Associated-graded convergence alone is insufficient:
Hausdorffness of this actual classical filtration is an explicit hypothesis.
It is a structural proof obligation, not an additional numerical A/C input. -/
theorem classical_stem125_filtration26_zero (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 125) : a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have hpage (s : ℕ) (hs : 26 ≤ s) :
        Subsingleton ((sequence D .sphere).Page 5 (s, (s : ℤ) + 125)) := by
      by_cases h64 : s ≤ 64
      · exact stem125_e5_zero_finite I s hs h64
      · exact sphere_page_zero_stem125_tail (D := D) V 5 s (by omega) (by omega)
    have hstep (s : ℕ) (hs : 26 ≤ s)
        (has : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum s 125) :
        a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum (s + 1) 125 := by
      let E := (sequence D .sphere).ssData (s, (s : ℤ) + 125)
      haveI : Subsingleton (E.page 3) := hpage s hs
      have hInf (z : E.eInfty) : z = 0 := by
        haveI : Epi (E.pageπ ⊤) := inferInstanceAs
          (Epi (CategoryTheory.Limits.cokernel.π _))
        obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance z
        have h := E.infinity_projection_eq_of_page_projection_eq 3 y 0
          (Subsingleton.elim _ _)
        change E.pageπ ⊤ y = 0
        simpa only [map_zero] using h
      have e : E.eInfty ≅
          (TowerDetection.filtration H.unit SphereSpectrum).associatedGraded s 125 := by
        dsimp only [E, sequence, object]
        simpa only [ClassicalObject.obj, add_sub_cancel_left] using
          (D.classicalConvergence .sphere).identification (s, (s : ℤ) + 125)
      have hmem : a ∈ (ModuleCat.subobjectModule _)
          ((TowerDetection.filtration H.unit SphereSpectrum).F s 125) := by
        simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using has
      obtain ⟨b, hb⟩ := hmem
      change ((TowerDetection.filtration H.unit SphereSpectrum).F s 125).arrow b = a at hb
      have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded
          s 125 b = 0 := by
        have h := congrArg e.hom (hInf
          (e.inv ((TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded s 125 b)))
        simpa only [← CategoryTheory.comp_apply, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, map_zero] using h
      have hnext := (subobject_cokernel_π_eq_zero_iff
        ((TowerDetection.filtration H.unit SphereSpectrum).F ((s : ℤ) + 1) 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).F s 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).mono s 125) b).mp hzero
      rw [hb] at hnext
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hnext
    apply S 125 a
    intro s
    by_cases hs : s ≤ 26
    · exact TowerDetection.filtrationSubmodule_antitone H.unit SphereSpectrum 125
        (by exact_mod_cast hs) ha
    · have h26 : 26 ≤ s := by omega
      clear hs
      induction s, h26 using Nat.le_induction with
      | base => exact ha
      | succ n hn ih =>
        simpa only [Nat.cast_add, Nat.cast_one] using hstep n hn ih

/-- Equality of two classical representatives follows only after proving
the higher-filtration indeterminacy zero.  The detection relation itself
remains associated-graded equality; it has not been replaced by strict equality. -/
theorem high125_detected_choice_unique (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a b : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.interpretation.sphere 25 150 highClass) a)
    (hb : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.interpretation.sphere 25 150 highClass) b) : a = b := by
  set_option backward.isDefEq.respectTransparency false in
    dsimp only [TowerDetection.Detects, ClassicalObject.obj] at ha hb
    obtain ⟨z, hz, a', ha', hga⟩ := ha
    obtain ⟨z', hz', b', hb', hgb⟩ := hb
    have heq := ((sequence D .sphere).ssData (25, 150)).infinity_projection_eq_of_page_projection_eq 0 z z' (hz.trans hz'.symm)
    have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded 25 (150 - 25) (a' - b') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (hga.symm.trans
        ((congrArg ((D.classicalConvergence .sphere).identification (25, 150)).hom heq).trans hgb))
    have hmem := (subobject_cokernel_π_eq_zero_iff
      ((TowerDetection.filtration H.unit SphereSpectrum).F 26 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).F 25 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).mono 25 (150 - 25))
      (a' - b')).mp hzero
    rw [map_sub, ha', hb'] at hmem
    have hab : a - b ∈
        TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 (150 - 25) := by
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hmem
    exact sub_eq_zero.mp (classical_stem125_filtration26_zero I V S (a - b) hab)

end
end KIP126.Computation.SphereAndCofiber
end
