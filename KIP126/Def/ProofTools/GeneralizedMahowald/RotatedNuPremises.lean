module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SourceBoundaryReview
import all KIP126.Def.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.Def.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Reverse
import KIP126.Def.Literature.Standard

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
set_option Elab.async false

private theorem unit_first_quotient_11_13_zero
    (a : BiHom 11 13 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) : a=0 := by
  let e : nuZero model .sphere ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ model.nu.unitIso
  obtain ⟨x,hx⟩ := firstLabel_surjective .sphere 2 13 (a≫XModLambdaN.map e.inv 1)
  have hx0 := sphere_ext_two_thirteen_zero x
  rw [hx0] at hx
  have hfirst0 : firstLabel model .sphere 2 13 (0 : Ambient model .sphere (2,13))=0 := by
    have cast_zero (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w=w')
        (he : BiHom m w A = BiHom m w' A) : he.mp 0=0 := by subst w'; rfl
    simp only [firstLabel,map_zero]
    rw [cast_zero _ _ _ _ (Int.add_zero 13)]
  rw [hfirst0] at hx
  have h := congrArg (fun f => f≫XModLambdaN.map e.hom 1) hx
  simpa only [Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id,model.quotients.functoriality.map_id,Category.comp_id,zero_comp] using h.symm

private theorem balanced_four_first_quotient_15_17_zero
    (a : BiHom 15 17 (XModLambdaN (Smn 4 4 : SyntheticSpectrum) 1)) : a=0 := by
  letI := model.exactness.shiftCommShift (4,4)
  letI := model.exactness.shiftExact (4,4)
  obtain ⟨Q,_,_⟩ := quotient_shift_exists model.quotients.coherence (4,4) 1
    (S_0_0 : SyntheticSpectrum)
  let e := suspInvarianceAddEquiv 11 13 4 4 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
  have hz : e.symm (a≫Q.hom)=0 := unit_first_quotient_11_13_zero _
  have h : a≫Q.hom=0 := by
    apply e.symm.injective
    simpa only [map_zero] using hz
  apply (cancel_mono Q.hom).mp
  simpa only [zero_comp] using h

private theorem rotated_nu_source_ext_zero
    (x : Ambient model rotatedNuRouteTriangle.Z (2,17)) : x=0 := by
  let e : nuZero model rotatedNuRouteTriangle.Z ≅ (Smn 4 4 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ rotated_nu_source_sphere
  let a := firstLabel model rotatedNuRouteTriangle.Z 2 17 x
  have ha : a≫XModLambdaN.map e.hom 1=0 :=
    balanced_four_first_quotient_15_17_zero _
  have ha0 : a=0 := by
    have h := congrArg (fun f => f≫XModLambdaN.map e.inv 1) ha
    simpa only [Category.assoc,←model.quotients.functoriality.map_comp,
      Iso.hom_inv_id,model.quotients.functoriality.map_id,Category.comp_id,zero_comp] using h
  have cast_zero_iff (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w=w')
      (he : BiHom m w A = BiHom m w' A) (z : BiHom m w A) :
      he.mp z=0 ↔ z=0 := by subst w'; rfl
  have ha' : (model.firstQuotient rotatedNuRouteTriangle.Z 0 2 17).symm x=0 := by
    exact (cast_zero_iff 15 (17+0) 17 _ (Int.add_zero 17) (by simp) _).mp ha0
  exact (model.firstQuotient rotatedNuRouteTriangle.Z 0 2 17).symm.injective
    (ha'.trans (map_zero _).symm)

private theorem rotated_nu_no_crossing :
    NoCrossingOn model rotatedNuRouteTriangle.Z 3 3 (1,16) := by
  refine ⟨by decide,by decide,?_⟩
  rintro ⟨a,b,ha,hap,hb,hbp,x,y,hd⟩
  have ha1 : a=1 := by omega
  have hb0 : b=0 := by omega
  subst a; subst b
  have hx : x=0 := rotated_nu_source_ext_zero x
  rw [hx] at hd
  obtain ⟨hdeg,xr,yr,hxr,hyr,heq,hne⟩ := hd
  have hxr0 : xr=0 := RepresentsOnPage.unique hxr (RepresentsOnPage.zero (by decide))
  rw [hxr0,map_zero] at heq
  exact hne heq.symm

private theorem regradeE2_zero {A : SyntheticAdamsSS} {i j : Tridegree}
    (h : i=j) : regradeE2 h (0 : A.E₂ i)=0 := by
  subst j
  rfl

private theorem target_nu_label_zero (Y : ClassicalObject) (s t : ℤ) (k : ℕ) :
    targetNuLabel model Y s t k 0=0 := by
  have cast_zero (A : SyntheticAdamsSS) (s t w w' : ℤ) (hw : w=w')
      (he : (A.E₂ (s,t,w) : Type)=(A.E₂ (s,t,w') : Type)) : he.mp 0=0 := by
    subst w'
    rfl
  simp only [targetNuLabel,map_zero]
  rw [cast_zero _ s t (t+0-k) (t-k) (by simp)]
  exact map_zero _

private def zero_finite_extension_witness (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (hr : 2≤r)
    (hl : (normalizedExponent model.classicalTower f : ℤ)≤n)
    (hu : n≤(r:ℤ)-2+normalizedExponent model.classicalTower f) :
    FiniteExtensionWitness model X Y f r n s t 0 0 := by
  refine {
    page_ge_two := hr
    length_lower := hl
    length_upper := hu
    source_cycle := ⟨0,RepresentsOnPage.zero (by exact_mod_cast hr)⟩
    target_cycle := ⟨0,RepresentsOnPage.zero (by omega)⟩
    source := 0
    target := 0
    source_rep := ?_
    target_rep := ?_
    equation := ?_ }
  · have hlabel : finiteSourceForExtension model X Y f (r-1) s t 0=0 := by
      simp only [finiteSourceForExtension,finiteNuLabel,map_zero,regradeE2_zero]
    rw [hlabel]
    exact HasInfinityRepresentative.zero _ 2 (by decide) _
  · have hlabel : finiteTargetForExtension model X Y f (r-1) n s t hl 0=0 := by
      simp only [finiteTargetForExtension,finiteTargetLabel,target_nu_label_zero,
        map_zero,regradeE2_zero]
    rw [hlabel]
    exact HasInfinityRepresentative.zero _ 2 (by decide) _
  · apply (tower_extension_iff _ _ _ _ _ _).mpr
    refine ⟨by omega,0,0,?_,?_,?_⟩
    · simp only [map_zero,zero_comp]
    · simp only [map_zero]
    · simp only [map_zero]

private def rotated_nu_g_zero_witness :
    FiniteExtensionWitness model rotatedNuRouteTriangle.Y rotatedNuRouteTriangle.Z
      rotatedNuRouteTriangle.g 2 0 4 18 0 0 :=
  zero_finite_extension_witness _ _ _ _ _ _ _ (by decide)
    (by rw [rotated_nu_g_exponent]; norm_num)
    (by rw [rotated_nu_g_exponent]; norm_num)

private def rotated_nu_h_zero_witness :
    FiniteExtensionWitness model rotatedNuRouteTriangle.Z (.shift 1 .sphere)
      rotatedNuRouteTriangle.h 3 2 1 16 0 0 :=
  zero_finite_extension_witness _ _ _ _ _ _ _ (by decide)
    (by rw [rotated_nu_h_exponent]; norm_num)
    (by rw [rotated_nu_h_exponent]; norm_num)

private theorem rotated_nu_g_zero_extension :
    FiniteExtension model rotatedNuRouteTriangle.Y rotatedNuRouteTriangle.Z
      rotatedNuRouteTriangle.g 2 0 4 18 0 0 :=
  ⟨rotated_nu_g_zero_witness⟩

private def rotated_nu_h_boundary_witness
    (sx : Ambient model (.shift 1 .sphere) (3,18))
    (hb : sx∈boundaries model (.shift 1 .sphere) 2 (3,18)) :
    FiniteExtensionWitness model rotatedNuRouteTriangle.Z (.shift 1 .sphere)
      rotatedNuRouteTriangle.h 3 2 1 16 0 sx := by
  have hb' : sx∈boundaries model (.shift 1 .sphere)
      (1+2-normalizedExponent model.classicalTower rotatedNuRouteTriangle.h) (3,18) := by
    simpa only [rotated_nu_h_exponent, Nat.cast_one, Int.reduceAdd, Int.reduceSub] using hb
  simpa only [zero_add] using finite_extension_target_add_boundary
    rotatedNuRouteTriangle.Z (.shift 1 .sphere) rotatedNuRouteTriangle.h
    3 2 1 16 0 0 sx rotated_nu_h_zero_witness hb'

private theorem rotated_nu_h_boundary_extension
    (sx : Ambient model (.shift 1 .sphere) (3,18))
    (hb : sx∈boundaries model (.shift 1 .sphere) 2 (3,18)) :
    FiniteExtension model rotatedNuRouteTriangle.Z (.shift 1 .sphere)
      rotatedNuRouteTriangle.h 3 2 1 16 0 sx :=
  ⟨rotated_nu_h_boundary_witness sx hb⟩

private theorem rotated_nu_remaining_premises :
    ∃ sx : Ambient model (.shift 1 .sphere) (3,18),
      (model.classicalSuspension .sphere).DesuspendsClass 3 18 sx mh2BoundaryClass ∧
      FiniteExtension model rotatedNuRouteTriangle.Z (.shift 1 .sphere)
        rotatedNuRouteTriangle.h 3 2 1 16 0 sx ∧
      NoCrossingOn model rotatedNuRouteTriangle.Z 3 3 (1,16) ∧
      FiniteExtension model .nuCofiber rotatedNuRouteTriangle.Z
        rotatedNuRouteTriangle.g 2 0 4 18 0 0 := by
  obtain ⟨sx,hsx,hb,_⟩ := mh2BoundaryClass_suspends_nonzero
  exact ⟨sx,hsx,rotated_nu_h_boundary_extension sx hb,
    rotated_nu_no_crossing,rotated_nu_g_zero_extension⟩

end
end KIP126.ProofTools.Internal.Mahowald
