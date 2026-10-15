module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Computation.Lambda


@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

section
open CategoryTheory.Limits KIP126.Classical.Adams.PageRepresentatives KIP126.Computation.SphereAndCofiber
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
/-- In weight128 the remaining classical incoming sources are in the vanishing
half-plane. Thus classical low-filtration E∞ vanishing also kills the full
synthetic associated grades, including possible finite-boundary quotients. -/
private theorem nu124_low_zero_permanent_quotient_zero_of_stable_boundaries
    (X : C) (p : ℤ×ℤ) (b : ℤ)
    (hzero : Subsingleton ((adamsTowerInternalSpectralSequence H.unit X).ssData p).eInfty)
    (hB : ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ⊤ =
      ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ↑(b-1).toNat) :
    Subsingleton (PermanentQuotient H X b p) := by
  classical
  let E := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have heq : LinearMap.range (boundaryMap H X ⊤ p).hom = boundaries H X b p := by
    have hh (B B' : Subobject E.V) (h : B ≤ E.Z 0) (h' : B' ≤ E.Z 0)
        (he : B = B') :
        LinearMap.range (Subobject.ofLE B _ h ≫ E.pageπ 0).hom =
          LinearMap.range (Subobject.ofLE B' _ h' ≫ E.pageπ 0).hom := by
      subst B'
      rfl
    exact hh _ _ _ _ hB
  have hcycles : permanentCycles H X p ≤ boundaries H X b p := by
    rintro x ⟨z,hz⟩
    have hz0 : E.pageπ ⊤ z = 0 := hzero.elim _ _
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤)) z).mp hz0
    rw [← heq]
    refine ⟨y,?_⟩
    have hfactor : Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤) ≫
        cycleMap H X ⊤ p = boundaryMap H X ⊤ p := by
      dsimp only [cycleMap,boundaryMap,E]
      rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    change boundaryMap H X ⊤ p y = x
    rw [← hfactor,CategoryTheory.comp_apply,hy]
    exact hz
  have hall (a : PermanentQuotient H X b p) : a = 0 := by
    obtain ⟨x⟩ := a
    exact (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr (hcycles x.property)
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩



private theorem nu124_low_zero
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (s : ℤ) (hs : s < 10)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData
      (s,124+s)).eInfty) :
    Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty) := by
  classical
  by_cases hw : 128 ≤ 124+s
  · let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C := C))
    have hin (r : ℤ) (hr : s-2 ≤ r) : E.d r ((s,124+s)-E.diffDeg r) = 0 := by
      have hi : (s,124+s)-E.diffDeg r = (s-r,(s-r)+125) := by
        change (s,124+s)-(r,r-1) = _
        ext <;> dsimp; omega
      rw [hi]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) a
    have hB := boundaries_top_eq_of_d_eq_zero E (s-2) (by change (2:ℤ)≤s-2; omega)
      (s,124+s) hin
    have hB' : (E.ssData (s,124+s)).B ⊤ =
        (E.ssData (s,124+s)).B ↑(1+(124+s)-128-1).toNat := by
      change (E.ssData (s,124+s)).B ⊤ = (E.ssData (s,124+s)).B ↑(s-2-2).toNat at hB
      simpa only [show s-2-2 = 1+(124+s)-128-1 by omega] using hB
    haveI := nu124_low_zero_permanent_quotient_zero_of_stable_boundaries SphereSpectrum (s,124+s)
      (1+(124+s)-128) hz hB'
    exact (A.eInfty.presentation.nuWindow SphereSpectrum (s,124+s) 128 hw).injective.subsingleton
  · haveI : Subsingleton (nuEInftyModel H (SphereSpectrum (C := C)) (s,124+s) 128) := by
      simp only [nuEInftyModel,hw,ite_false]
      infer_instance
    exact (A.eInfty.presentation.nu SphereSpectrum (s,124+s) 128).injective.subsingleton

private theorem stem124_weight128_filtration_ten
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (hc : ∀ s : ℤ, s < 10 → Subsingleton
      ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,s+124)).eInfty)
    (a : BiHom 124 128 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a := by
  apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    0 10 124 128 (by omega) ?_ a).mp
  · refine ⟨a,?_⟩
    change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
    rw [adamsTowerMap_self]
    change a ≫ 𝟙 _ = a
    exact Category.comp_id a
  · intro s hs hs10
    have hz : Subsingleton
        ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,124+s)).eInfty := by
      simpa only [add_comm] using hc s hs10
    haveI := nu124_low_zero A I s hs10 hz
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (s,124+s,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (s,124+s,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp,← Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
end

end
end KIP126.Main.SectionSeven
