module

public import KIP126.Def.AdamsSynthetic.Conditions.Predicates
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data
public import KIP126.Main.Computation.Lambda
import all KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
import all KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection
import all KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
import all KIP126.Main.Computation.SphereAndCofiber.NamedSurvival

@[expose] public section

open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : AdamsComparison H M Syn) (L : SphereAdamsClasses H)

namespace KIP126.Main.Stem126.Conditions
/-- The proposition expressing LWX Lemmas 7.10 and 7.11:
condition (4) varies θ₅ in π_(62,64), whereas condition (5) varies
[h₀²x₁₂₄,₈] in π_(124,134). Establishing the equivalences also requires
the existence of admissible representatives. Its proof is
`ChoiceIndependence.square_and_eta_detection_choice_equivalence_proved` below. -/
def square_and_eta_detection_choice_equivalence (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toAdamsComparisonData η →
    (Theta5SquareNonzeroDetection M D.toAdamsComparisonData L ↔
      ∀ θ, ThetaChoice M D.toAdamsComparisonData θ → Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ) ∧
    (EtaExtensionDetection M D.toAdamsComparisonData L η ↔
      ∀ u, UChoice M D.toAdamsComparisonData L u → EtaExtensionDetectionAt M D.toAdamsComparisonData L η u)
end KIP126.Main.Stem126.Conditions

end

/-! LWX Lemmas 7.10–7.11. The weight-131 ambiguity calculation is adapted
from develop commit 53f42f9, Main/Internal/Choice/Completion (MIT). It uses
the existing local comparison and computation inputs on one common sphere. -/
@[expose] public section
namespace KIP126.Main.ChoiceIndependence
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Kervaire
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.SphereAndCofiber
open private tail_af5 from KIP126.Main.Computation.SphereAndCofiber.NamedSurvival
open private theta_square_choice_invariance from KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
open private eta_detection_sphere_frame_of_permanent_quotient
  eta_detection_theta_detection_step eta_detection_sphere_zero_weight_label_10_134
  eta_detection_eta_lambda3_right eta_detection_detects_of_difference_in_next_filtration
  eta_detection_u_choice_exists from KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection
open private stem124_af13_exhaustion from KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

private theorem no_outgoing_stem125_low_late (I : AdamsComputationTheorems D L G)
    (s r : ℤ) (hs : s≤5) (hr : 5≤r)
    (x : (sequence D .sphere).Page r (s,s+125)) :
    (sequence D .sphere).d r (s,s+125) x=0 := by
  by_cases hs5 : s=5
  · subst s
    have hz := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
      5 r 5 130 (by decide) hr (tail_af5 I)
    rw [hz.elim x 0,map_zero]
  · exact no_outgoing_stem125_low I s (by omega) r (by omega) x

private theorem choice_quotient_frame_late
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤5) (hk : 3≤k)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low_late I (s-r) r (by omega) (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  refine ⟨x',rfl,?_⟩
  have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hzero : P.pageπ ⊤ z'=0) :
      PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
    have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
    change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
      (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
    rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
    refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
    rw [←hb]
    change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
      (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
    congr 1
    dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  rcases hall (P.pageπ ⊤ z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_infinity_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x ∈ _
    rw [←hz',←hz,←map_sub]
    exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])

private theorem choice_sphere_frame_late
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤5) (hk : 3≤k)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  exact eta_detection_sphere_frame_of_permanent_quotient BHS s t k x
    (choice_quotient_frame_late I s t k hst hsk hk x hx)

private theorem stem124_weight131_filtration11_branches {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (x13 : E2 H SphereSpectrum 13 137)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 131 (S_0_0 : Syn))
    (ha11 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a) :
    SphereDetected D 13 137 6 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 7 b=a := by
  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 4) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
        have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      11 13 124 131 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-131) (j,124+j)) :=
      permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 131 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,131)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,131)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,131)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,131)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have ha13 := hgap ha11
  have hf13 := choice_sphere_frame_late I BHS 13 137 6 (by omega) (by omega) (by decide) x13 h13
  rcases eta_detection_theta_detection_step (13,137,131) (D.sphereE2 13 137 6 x13) hf13 a ha13 with hdet|ha14
  · exact Or.inl hdet
  right
  have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have h := BHS.filtration_lambda .sphere 124 131 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 7 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb

private theorem eta_weight131_branches_filtration_fifteen {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (b : BiHom 124 131 (S_0_0 : Syn))
    (hbranch : SphereDetected D 13 137 6 (I.interpretation.sphere 13 137 correction)
        b ∨
      ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 7 a=b) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η b) := by
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  rcases hbranch with h13 | ⟨a,ha⟩
  · have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
        (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)=0 := by
      have h := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
      dsimp only at h
      rw [I.distinguishedClasses.h1] at h
      exact h.symm.trans SF.h1_correction_zero
    have hd := D.multiplicationCompatible 1 2 13 137 0 6
      (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)
      η b hηd h13.1
    change Detects D.sphereConvergence (14,139,133)
      (D.sphereE2 14 139 6 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
        (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)))
      (sphereProduct η b) at hd
    rw [hp,map_zero] at hd
    exact detects_zero_filtration D.sphereConvergence (14,139,133) hd
  · have had := D.comparisonCompatible.homotopy_lambda 14 138 7 a
    rw [ha] at had
    have hd := D.multiplicationCompatible 1 2 14 138 0 7
      (Sphere.Internal.hi H M 1) (D.sphereFirstQuotient 14 138 (quotientClass 1 a))
      η b hηd had
    change Detects D.sphereConvergence (15,140,133) _ (sphereProduct η b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,133)).arrow a'∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,133)))
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,133)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm


private theorem u_eta_difference_fifteen
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (u v : BiHom 124 134 (S_0_0 : Syn))
    (hu : UChoice M D.toAdamsComparisonData L u) (hv : UChoice M D.toAdamsComparisonData L v) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
      ((show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 3 (sphereProduct η u)) -
        (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 3 (sphereProduct η v))) := by
  have hu0 := eta_detection_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) u hu.1
  have hv0 := eta_detection_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) v hv.1
  have hdu := D.comparisonCompatible.homotopy_lambda 10 134 3 u
  have hdv := D.comparisonCompatible.homotopy_lambda 10 134 3 v
  rw [hu0] at hdu
  rw [hv0] at hdv
  have hd := detects_sub_filtration D.sphereConvergence (10,134,131) hdu hdv
  have he := eta_weight131_branches_filtration_fifteen I SF η hη _
    (stem124_weight131_filtration11_branches I BHS _ (stem124_af13_exhaustion I SF)
      SF.e5_stem124_af11 SF.e4_stem124_af12 _ hd)
  have hlinear : sphereProduct η
      ((show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 3 u) -
        (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 3 v)) =
      (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 3 (sphereProduct η u)) -
        (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 3 (sphereProduct η v)) := by
    have hh : sphereProduct η
        ((show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 3 u) -
          (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 3 v)) =
        sphereProduct η (lambdaMultiply 3 u) - sphereProduct η (lambdaMultiply 3 v) := by
      simp only [sphereProduct, Int.reduceAdd, Int.reduceSub, Nat.cast_ofNat, Preadditive.comp_sub]
    rw [hh, eta_detection_eta_lambda3_right D, eta_detection_eta_lambda3_right D]
  rwa [hlinear] at he

/-- Lemma 7.10: the nonzero square detection is independent of the admissible
θ₅ representative. The BX source supplies one admissible representative. -/
theorem theta5_square_detection_choice_equivalence
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (RL : RealizationDetectionData D) {η : BiHom 1 2 (S_0_0 : Syn)}
    (CL : ClassicalTheorems D η) (AF : SphereActionFiltrationCompatible D)
    (BX : BXDistinguishedThetaTheorem D η) :
    Theta5SquareNonzeroDetection M D.toAdamsComparisonData L ↔
      ∀ theta, ThetaChoice M D.toAdamsComparisonData theta →
        Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta := by
  constructor
  · rintro ⟨theta',htheta',hc⟩ theta htheta
    exact theta_square_choice_invariance I BHS RL CL AF theta theta' htheta htheta' hc
  · intro h
    obtain ⟨theta,htheta,_,_⟩ := BX
    exact ⟨theta,htheta.2.1,h theta htheta.2.1⟩

/-- Lemma 7.11: multiplying by λ³η carries the ambiguity between any two U
representatives into F15, so their F14 detection conditions agree. -/
theorem eta_extension_detection_choice_equivalence
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η) :
    EtaExtensionDetection M D.toAdamsComparisonData L η ↔
      ∀ u, UChoice M D.toAdamsComparisonData L u →
        EtaExtensionDetectionAt M D.toAdamsComparisonData L η u := by
  constructor
  · rintro ⟨v,hv,hdet⟩ u hu
    exact eta_detection_detects_of_difference_in_next_filtration
      D.sphereConvergence (14,139,133) hdet
      (u_eta_difference_fifteen I BHS SF η hη u v hu hv)
  · intro h
    obtain ⟨u,hu⟩ := eta_detection_u_choice_exists I BHS SF
    exact ⟨u,hu,h u hu⟩

/-- The previously recorded proposition for Lemmas 7.10–7.11, now proved
from the unchanged literature and computation inputs. -/
theorem square_and_eta_detection_choice_equivalence_proved
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (RL : RealizationDetectionData D) {η : BiHom 1 2 (S_0_0 : Syn)}
    (CL : ClassicalTheorems D η) (AF : SphereActionFiltrationCompatible D)
    (BX : BXDistinguishedThetaTheorem D η) (SF : Derived.SphereFacts I.interpretation) :
    KIP126.Main.Stem126.Conditions.square_and_eta_detection_choice_equivalence M D L η := by
  intro hη
  exact ⟨theta5_square_detection_choice_equivalence I BHS RL CL AF BX,
    eta_extension_detection_choice_equivalence I BHS SF η hη⟩

end
end KIP126.Main.ChoiceIndependence
end
