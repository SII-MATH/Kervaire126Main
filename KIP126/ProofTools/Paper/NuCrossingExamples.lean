module

public import KIP126.ProofTools.Language
public import KIP126.ProofTools.StandardSpecializations
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import KIP126.E2Computation

/-! The actual E₂ ν relation and the crossing checks of AimPaper 5.13.
The page-two crossing range is empty. The later checks retain the actual
first-quotient operation and do not use the disputed crossing equivalence.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace NuCrossingCoordinates
open KIP126.Computation KIP126.Computation.Standard

private def rwMonomial {s t s' t' : ℕ} (hs : s=s') (ht : t=t')
    (a : SourceMonomial archive.generators s t) : SourceMonomial archive.generators s' t' :=
  hs ▸ ht ▸ a
private def h0Word : SourceMonomial archive.generators 1 1 :=
  rwMonomial rfl rfl (.generator (archive.atomIndex .h0))
private def h4Word : SourceMonomial archive.generators 1 16 :=
  rwMonomial rfl rfl (.generator (archive.atomIndex .h4))
private def a : model.classical.sphere.Page 2 (4,34) :=
  product h0 (product (r := (3,33)) h0 (product (r := (2,32)) h4 h4))
private theorem a_basis :
    (coordinates 4 34 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1) = a := by
  rw [coordinates_basis]
  have hword : archive.basisMonomial 4 34 ⟨0,by decide⟩ =
      .mul h0Word (.mul h0Word (.mul h4Word h4Word)) := by rfl
  rw [hword]
  have h0v : h0Word.value sourceData sourceGenerator = sourceData.atom .h0 :=
    sourceAtom_agrees .h0
  have h4v : h4Word.value sourceData sourceGenerator = sourceData.atom .h4 :=
    sourceAtom_agrees .h4
  simp only [SourceMonomial.value,h0v,h4v]
  have hp44 := comparison_product 1 16 1 16 (by decide)
    (sourceData.atom .h4) (sourceData.atom .h4)
  have hp04 := comparison_product 1 1 2 32 (by decide) (sourceData.atom .h0)
    (sourceData.product 1 16 1 16 (sourceData.atom .h4) (sourceData.atom .h4))
  have hp00 := comparison_product 1 1 3 33 (by decide) (sourceData.atom .h0)
    (sourceData.product 1 1 2 32 (sourceData.atom .h0)
      (sourceData.product 1 16 1 16 (sourceData.atom .h4) (sourceData.atom .h4)))
  rw [hp00,hp04,hp44,comparison_h0,comparison_h4]
  rfl


private theorem one_coordinate_cases (x : Fin 1 →₀ ZMod 2) :
    x=0 ∨ x=Finsupp.single 0 1 := by
  rcases (by decide : ∀ c : ZMod 2, c=0 ∨ c=1) (x 0) with h | h
  · left
    apply Finsupp.ext
    intro i
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi,Finsupp.zero_apply] using h
  · right
    apply Finsupp.ext
    intro i
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi,Finsupp.single_eq_same] using h

private theorem a_cases (x : model.classical.sphere.Page 2 (4,34)) : x=0 ∨ x=a := by
  let e : model.classical.sphere.Page 2 (4,34) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) :=
    coordinates 4 34 (by decide)
  rcases one_coordinate_cases (e x) with h | h
  · left
    apply e.injective
    exact h.trans e.map_zero.symm
  · right
    apply e.injective
    have ha : e.symm (Finsupp.single 0 1)=a := a_basis
    exact h.trans ((e.apply_symm_apply _).symm.trans (congrArg e ha))

open CategoryTheory KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.Literature.Standard

private theorem pairing_right_differential_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)}
    (P : SSPairing E E E) (hstart : E.r₀≤2)
    (p q u : ℤ×ℤ) (x : E.Page 2 p) (y : E.Page 2 q) (z : E.Page 2 u)
    (hx : ReachesPage E 3 p x)
    (hxy : ReachesPage E 3 (p+q) (P.pair 2 p q x y))
    (hy : HasDifferential E 2 q u y z) : P.pair 2 p u x z=0 := by
  obtain ⟨hdeg,hd⟩ := hy.eq_on_page_two
  subst u
  simp only [eqToHom_refl,Category.comp_id] at hd
  have hdx := (PageThree.reachesPage_iff_d2_eq_zero hstart p x).mp hx
  have hdxy := (PageThree.reachesPage_iff_d2_eq_zero hstart (p+q) _).mp hxy
  have H := P.leibniz 2 p q x y
  rw [hdxy,hdx,hd] at H
  simp only [LinearMap.zero_apply,map_zero,zero_add] at H
  let T := transportPage E 2 (show p+(q+E.diffDeg 2)=(p+q)+E.diffDeg 2 by ac_rfl)
  change 0 = (if P.parity p=1 then (-1:ℤ) else 1) • T (P.pair 2 p (q+E.diffDeg 2) x z) at H
  have hz : T (P.pair 2 p (q+E.diffDeg 2) x z)=0 := by
    split_ifs at H <;> simpa using H.symm
  have hinj : Function.Injective T := by
    apply (ModuleCat.mono_iff_injective _).mp
    dsimp only [T,transportPage]
    infer_instance
  have hT0 : T 0=0 := T.hom.map_zero
  exact hinj (hz.trans hT0.symm)

private theorem h2_h0_h4_square_zero :
    product (r := (4,37)) h2 (product (r := (3,33)) h0
      (product (r := (2,32)) h4 h4))=0 := by
  let I := sphereMappingAdamsIso KIP126.Literature.Standard.closedTensor model.classical
  let S : MappingObject (fun X : Spectrum => X=SphereSpectrum) := ⟨SphereSpectrum,rfl⟩
  let P := (KIP126.Literature.Standard.mappingComposition.pairing S S S).ssPairing
  let E := model.classical.obj (mappingSpectrum KIP126.Literature.Standard.closedTensor SphereSpectrum SphereSpectrum)
  have hstart : E.r₀≤2 := by simpa only [E,model.classical.firstPage] using (le_refl (2:ℤ))
  have hinv (r : ℤ) (p : ℤ×ℤ) (v : model.classical.sphere.Page r p) :
      I.hom.pageMap r p (I.inv.pageMap r p v)=v := by
    change (I.inv.pageMap r p ≫ I.hom.pageMap r p) v=v
    rw [←SpectralSequenceMorphism.pageMap_comp,I.inv_hom_id,SpectralSequenceMorphism.pageMap_id]
    rfl
  have hhom (r : ℤ) (p : ℤ×ℤ) (v : E.Page r p) :
      I.inv.pageMap r p (I.hom.pageMap r p v)=v := by
    change (I.hom.pageMap r p ≫ I.inv.pageMap r p) v=v
    rw [←SpectralSequenceMorphism.pageMap_comp,I.hom_inv_id,SpectralSequenceMorphism.pageMap_id]
    rfl
  let x := I.inv.pageMap 2 (1,4) h2
  let y := I.inv.pageMap 2 (1,32) h5
  let b := product (r := (3,33)) h0 (product (r := (2,32)) h4 h4)
  let z := I.inv.pageMap 2 (3,33) b
  have h2reach : ReachesPage model.classical.sphere 3 (1,4) h2 := by
    apply (PageThree.reachesPage_iff_d2_eq_zero (by simpa only [model.classical.firstPage] using (le_refl (2:ℤ))) _ _).mpr
    have hall : ∀ a : model.classical.sphere.Page 2 ((1,4)+model.classical.sphere.diffDeg 2), a=0 := by
      rw [model.classical.differentialDegree]
      intro a
      let e := coordinates 3 5 (by decide)
      haveI : Subsingleton (Fin (archive.basisCount 3 5) →₀ ZMod 2) := by
        change Subsingleton (Fin 0 →₀ ZMod 2)
        infer_instance
      apply e.injective
      exact Subsingleton.elim _ _
    exact hall _
  obtain ⟨x3,hx3⟩ := h2reach
  have hx : ReachesPage E 3 (1,4) x := ⟨I.inv.pageMap 3 (1,4) x3,I.inv.representsOnPage hx3⟩
  have hpair : I.hom.pageMap 2 (2,36) (P.pair 2 (1,4) (1,32) x y)=
      KIP126.Literature.Standard.hiProduct 2 5 := by
    have h := KIP126.Literature.Standard.mappingSphereCompatibility.product (1,4) (1,32) x y
    change I.hom.pageMap 2 (2,36) (P.pair 2 (1,4) (1,32) x y)=
      model.sphereAlgebra.product (1,4) (1,32)
        (I.hom.pageMap 2 (1,4) x) (I.hom.pageMap 2 (1,32) y) at h
    dsimp only [x,y] at h
    rw [hinv,hinv] at h
    exact h
  obtain ⟨v,hv⟩ := KIP126.Literature.Standard.mahowald_tangora_h2_h5_d3
  obtain ⟨v3,hv3,_⟩ := hv.source_survives
  have hxy : ReachesPage E 3 (2,36) (P.pair 2 (1,4) (1,32) x y) := by
    refine ⟨I.inv.pageMap 3 (2,36) v3,?_⟩
    have h := I.inv.representsOnPage hv3
    rw [←hpair,hhom] at h
    exact h
  have hy : HasDifferential E 2 (1,32) (3,33) y z := by
    have h := (KIP126.Literature.Standard.adamsOneLine_d2 5 (by decide)).toHasDifferential
    have hb : KIP126.Literature.oneLineTarget model 5=b := by rfl
    rw [hb] at h
    exact I.inv.hasDifferential h
  have hz := pairing_right_differential_zero P hstart (1,4) (1,32) (3,33) x y z hx hxy hy
  have H := congrArg (I.hom.pageMap 2 (4,37)) hz
  rw [map_zero] at H
  have hc := KIP126.Literature.Standard.mappingSphereCompatibility.product (1,4) (3,33) x z
  change I.hom.pageMap 2 (4,37) (P.pair 2 (1,4) (3,33) x z)=
    model.sphereAlgebra.product (1,4) (3,33)
      (I.hom.pageMap 2 (1,4) x) (I.hom.pageMap 2 (3,33) z) at hc
  dsimp only [x,z] at hc
  rw [hinv,hinv] at hc
  exact hc.symm.trans H

private theorem h2_a_zero : product (r := (5,38)) h2 a=0 := by
  let b := product (r := (3,33)) h0 (product (r := (2,32)) h4 h4)
  have h₁ : product (r := (5,38)) (product (r := (2,5)) h2 h0) b=
      product (r := (5,38)) h2 (product (r := (4,34)) h0 b) :=
    eq_of_heq (model.sphereAlgebra.assoc (1,4) (1,1) (3,33) h2 h0 b)
  have hc : product (r := (2,5)) h2 h0=product (r := (2,5)) h0 h2 :=
    KIP126.Computation.Table.product_comm 1 4 1 1 (by decide) h2 h0
  have h₂ : product (r := (5,38)) (product (r := (2,5)) h0 h2) b=
      product (r := (5,38)) h0 (product (r := (4,37)) h2 b) :=
    eq_of_heq (model.sphereAlgebra.assoc (1,1) (1,4) (3,33) h0 h2 b)
  change product (r := (5,38)) h2 (product (r := (4,34)) h0 b)=0
  rw [←h₁,hc,h₂]
  have hb : product (r := (4,37)) h2 b=0 := h2_h0_h4_square_zero
  rw [hb]
  change model.sphereAlgebra.product (1,1) (4,37) h0 0=0
  exact map_zero _


end NuCrossingCoordinates

/-- The specified ordinary threefold suspension of the standard h₅ label,
with the actual final sphere shift map retained. -/
public def IsSphereThreeH5
    (x : Ambient model (.shift 3 .sphere) (1,35)) : Prop :=
  let e :
      ((ClassicalObject.shift 1 (.shift 1 (.shift 1 .sphere))).obj model.auxiliary) ≅
        ((ClassicalObject.shift 3 .sphere).obj model.auxiliary) :=
    (shiftFunctor Spectrum (1:ℤ)).mapIso
      (((shiftFunctorAdd' Spectrum (1:ℤ) 1 2 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm) ≪≫
      ((shiftFunctorAdd' Spectrum (2:ℤ) 1 3 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm
  ∃ (x1 : Ambient model (.shift 1 .sphere) (1,33))
    (x2 : Ambient model (.shift 1 (.shift 1 .sphere)) (1,34))
    (x3 : Ambient model (.shift 1 (.shift 1 (.shift 1 .sphere))) (1,35)),
    (model.classicalSuspension .sphere).DesuspendsClass 1 33 x1
      (model.standardClasses.standardHi 5) ∧
    (model.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 1 34 x2 x1 ∧
    (model.classicalSuspension (.shift 1 (.shift 1 .sphere))).DesuspendsClass
      1 35 x3 x2 ∧
    (model.classical.map e.hom).pageMap 2 (1,35) x3 = x

private theorem exists_nonzero_sphere_three_h5 :
    ∃ x : Ambient model (.shift 3 .sphere) (1,35), IsSphereThreeH5 x ∧ x ≠ 0 := by
  have h5ne : model.standardClasses.standardHi 5 ≠ 0 := by
    intro hz
    apply h5Q1_ne_zero
    simp only [h5Q1,hz,map_zero]
  obtain ⟨x1,hx1⟩ := exists_suspendsClass .sphere 1 33 (model.standardClasses.standardHi 5)
  obtain ⟨x2,hx2⟩ := exists_suspendsClass (.shift 1 .sphere) 1 34 x1
  obtain ⟨x3,hx3⟩ := exists_suspendsClass (.shift 1 (.shift 1 .sphere)) 1 35 x2
  have h1 : x1 ≠ 0 := (desuspendsClass_ne_zero_iff .sphere 1 33 x1 _ hx1).mpr h5ne
  have h2 : x2 ≠ 0 := (desuspendsClass_ne_zero_iff (.shift 1 .sphere) 1 34 x2 x1 hx2).mpr h1
  have h3 : x3 ≠ 0 := (desuspendsClass_ne_zero_iff (.shift 1 (.shift 1 .sphere))
    1 35 x3 x2 hx3).mpr h2
  let e := KIP126.ProofTools.Paper.NumericalExamples.tripleSphereShiftIso
  let x := (model.classical.map e.hom).pageMap 2 (1,35) x3
  refine ⟨x,⟨x1,x2,x3,hx1,hx2,hx3,rfl⟩,?_⟩
  intro hx
  apply h3
  have h := congrArg (fun z => (model.classical.map e.inv).pageMap 2 (1,35) z) hx
  have hinv : (model.classical.map e.hom).pageMap 2 (1,35) ≫
      (model.classical.map e.inv).pageMap 2 (1,35) = 𝟙 _ := by
    rw [←SpectralSequenceMorphism.pageMap_comp,←model.classical.map_comp,
      Iso.hom_inv_id,model.classical.map_id,SpectralSequenceMorphism.pageMap_id]
  simpa only [x,←ModuleCat.comp_apply,hinv,ModuleCat.id_apply,map_zero] using h

private theorem positive_nu_source_q1_unique
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (a b : BiHom 34 36 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1))
    (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  let Q := (model.quotients.functoriality.functor 1).mapIso positiveNuSphereThreeIso
  let E : BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≃
      BiHom 34 36 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1) :=
    (susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).trans
      (Iso.homCongr (Iso.refl _) (κ.symm ≪≫ Q.symm))
  have hzero : E 0 = 0 := by
    simp [E,Iso.homCongr,susp_invariance]
  apply E.symm.injective
  apply h5Q1_unique
  · intro hz
    apply ha
    have h := congrArg E hz
    simpa only [Equiv.apply_symm_apply,hzero] using h
  · intro hz
    apply hb
    have h := congrArg E hz
    simpa only [Equiv.apply_symm_apply,hzero] using h

private theorem h5_nu_q1_source_detects
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (x : Ambient model (.shift 3 .sphere) (1,35)) (hx : x ≠ 0) :
    Detects (model.convergence (.quotient 1 (.shift (0,1) (.nu (.shift 3 .sphere)))))
      (1,35,36) (regradeE2 (by simp) (finiteNuLabel model (.shift 3 .sphere) 1 1 1 35 0 x))
      (shiftHomotopyClass (3,4) (31,32) h5Q1 ≫ κ.inv ≫
        XModLambdaN.map positiveNuSphereThreeIso.inv 1) := by
  let c := shiftHomotopyClass (3,4) (31,32) h5Q1 ≫ κ.inv ≫
    XModLambdaN.map positiveNuSphereThreeIso.inv 1
  have hcne : c ≠ 0 := by
    intro hz
    have hh := congrArg (fun z => z ≫ XModLambdaN.map positiveNuSphereThreeIso.hom 1 ≫ κ.hom) hz
    let Q := (model.quotients.functoriality.functor 1).mapIso positiveNuSphereThreeIso
    change (shiftHomotopyClass (3,4) (31,32) h5Q1 ≫ κ.inv ≫ Q.inv) ≫ Q.hom ≫ κ.hom = 0 ≫ _ at hh
    simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id,zero_comp] at hh
    apply h5Q1_ne_zero
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (3,4)).map_injective
    rw [Functor.map_zero]
    apply (cancel_epi ((SyntheticCategory.biShift_comp (31,32) (3,4)).inv.app S_0_0)).mp
    change shiftHomotopyClass (3,4) (31,32) h5Q1 = _
    simpa only [comp_zero] using hh
  obtain ⟨x0,hx0cycle,hx0det⟩ := positive_finite_source_label_exists (.shift 3 .sphere)
    1 (by decide) 1 35 c
  have hx0first := shifted_finite_source_first (.shift 3 .sphere) 1 (by decide)
    1 1 35 x0 c hx0det
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hx0first
  have hx0ne : (model.firstQuotient (.shift 3 .sphere) 1 1 35).symm x0 ≠ 0 := by
    rw [←hx0first]
    exact hcne
  have hlabelne : (model.firstQuotient (.shift 3 .sphere) 1 1 35).symm x ≠ 0 := by
    intro hz
    apply hx
    have hh := congrArg (model.firstQuotient (.shift 3 .sphere) 1 1 35) hz
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh
  have hx0eq : x0 = x := (model.firstQuotient (.shift 3 .sphere) 1 1 35).symm.injective
    (positive_nu_source_q1_unique κ _ _ hx0ne hlabelne)
  subst x0
  exact hx0det

/-- The actual E₂ ν extension of the ordinary threefold suspension of h₅. -/
public theorem paper5_8_nu_e2_extension :
    ∃ x : Ambient model (.shift 3 .sphere) (1,35),
      IsSphereThreeH5 x ∧
      FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
        2 1 1 35 x (KIP126.Literature.Standard.hiProduct 2 5) := by
  obtain ⟨x,hx,hxne⟩ := exists_nonzero_sphere_three_h5
  letI := model.exactness.shiftCommShift (3,4)
  letI := model.exactness.shiftExact (3,4)
  obtain ⟨κ,hκ,_⟩ := quotient_shift_exists model.quotients.coherence (3,4) 1 (S_0_0:SyntheticSpectrum)
  let c := shiftHomotopyClass (3,4) (31,32) h5Q1 ≫ κ.inv ≫
    XModLambdaN.map positiveNuSphereThreeIso.inv 1
  let b := c ≫ XModLambdaN.map positiveNuNormalizedMap 1
  have hc := h5_nu_q1_source_detects κ x hxne
  have hbfirst : b = nativeFirstLabel .sphere 2 36 (KIP126.Literature.Standard.hiProduct 2 5) :=
    by simpa only [b,c,Category.assoc] using h5_actual_nu_source_quotient_image κ hκ
  have hb := first_label_detects_unshifted .sphere 1 (by decide) 2 36
    (KIP126.Literature.Standard.hiProduct 2 5) b (by
      simpa only [(model.quotients.tower _).rho_id,Category.comp_id,nativeFirstLabel] using hbfirst)
  refine ⟨x,hx,?_⟩
  apply positive_detected_pair_finite_page_two (.shift 3 .sphere) .sphere model.auxiliary.nuMap
    KIP126.Literature.Standard.nuCofiber_nu_exponent 1 35 x
    (KIP126.Literature.Standard.hiProduct 2 5) c b hc
    (by simpa [homotopyRegrade] using hb)
  rfl

/-- The first ν example has no crossing: the page-two definition allows
no positive displacement of the source. -/
public theorem paper5_13_nu_e2_no_crossing :
    FiniteNoCrossing model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
      2 1 1 35 := by
  rintro ⟨a, b, ha, hpage, _⟩
  omega

namespace NuCrossingAction

private theorem q1_sphere_action_actual_map_general
    (m w : ℤ)
    (unique:∀u v:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
    (ν:BiHom 3 4 (S_0_0:SyntheticSpectrum))
    (x:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
    homotopyRegrade (add_comm 3 m) (add_comm 4 w) (sphereAction ν x)=(susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫
      κ.inv≫XModLambdaN.map ν 1 := by
  classical
  have tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).Faithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    exact Functor.Faithful.of_comp_iso f
  let tensorLeft_sphere_fullyFaithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).FullyFaithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    letI := tensorLeft_sphere_faithful (-m) (-n)
    exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.ofFullyFaithful (𝟭 SyntheticSpectrum)).ofIso f.symm)
  have lambda_first_kills_unit_hom
      (f:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) :
      lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f=0 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.mayData.leftShift
    letI:=Standard.mayData.leftExact
    let l:BiHom 0 (-1) (S_0_0:SyntheticSpectrum):=lambdaPow 1 (S_0_0:SyntheticSpectrum)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫f
    have hl:quotientClass 1 l=0 := by
      change lambdaPow 1 (S_0_0:SyntheticSpectrum)≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=Standard.quotientAlgebra_sphere_action 1 (by decide) 0 (-1) 0 0 l z
    have hp:Standard.quotientAlgebraProduct (Standard.quotientAlgebra 1 (by decide)) (quotientClass 1 l) z=0 := by
      rw [hl]
      unfold Standard.quotientAlgebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:SyntheticSpectrum) 1) ◁ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 1 (S_0_0:SyntheticSpectrum))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-1) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1)):= by
        have hc := model.quotients.coherence.right_unit (0,-1) (S_0_0:SyntheticSpectrum)
        change (biShiftAddIso (0,-1) (0,0) (0,-1) (by decide)).hom.app (S_0_0:SyntheticSpectrum)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-1) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1))≫lambdaPow 1 (S_0_0:SyntheticSpectrum))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
       :
      Function.Surjective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_first_kills_unit_hom  f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective :
      Function.Injective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫f=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-1):=(biSuspensionIso 1 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply KIP126.ProofTools.Paper.NuNumericalExtensions.sphere_quotient_high_filtration_zero 1 (by decide) 1 (-1) 0 (by decide)
      exact KIP126.ProofTools.Paper.NuNumericalExtensions.filtration_zero (e.inv≫δ)
    have hd:δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd,comp_zero] using hδ
  have extend_unit_iso
      {S A:SyntheticSpectrum} (i:S⟶A)
      (hi:Function.Bijective (fun g:A⟶A=>i≫g))
      (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful) (tt:T.FullyFaithful)
      (eS:F.obj S≅T.obj S) (eA:F.obj A≅T.obj A) :
      ∃E:F.obj A≅T.obj A,F.map i≫E.hom=eS.hom≫T.map i := by
    have lift (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        (eA:F.obj A≅T.obj A) (f:F.obj S⟶T.obj A) :
        ∃g:F.obj A⟶T.obj A,F.map i≫g=f := by
      let z:=ff.preimage (f≫eA.inv)
      obtain ⟨g,hg⟩:=hi.2 z
      change i≫g=z at hg
      refine ⟨F.map g≫eA.hom,?_⟩
      rw [←Category.assoc,←F.map_comp,hg]
      have hz:F.map z=f≫eA.inv:=ff.map_preimage _
      rw [hz,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    have inj (F:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        {a b:F.obj A⟶F.obj A} (h:F.map i≫a=F.map i≫b) :a=b := by
      obtain ⟨a',rfl⟩:=ff.map_surjective a
      obtain ⟨b',rfl⟩:=ff.map_surjective b
      rw [←F.map_comp,←F.map_comp] at h
      exact congrArg F.map (hi.1 (ff.map_injective h))
    obtain ⟨f,hf⟩:=lift F T ff eA (eS.hom≫T.map i)
    obtain ⟨g,hg⟩:=lift T F tt eA.symm (eS.inv≫F.map i)
    have hfg:f≫g=𝟙 _ := by
      apply inj F ff
      rw [←Category.assoc,hf,Category.assoc,hg,←Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]
    have hgf:g≫f=𝟙 _ := by
      apply inj T tt
      rw [←Category.assoc,hg,Category.assoc,hf,←Category.assoc,Iso.inv_hom_id,Category.id_comp,Category.comp_id]
    exact ⟨⟨f,g,hfg,hgf⟩,hf⟩
  have q1_unit_tensor_iso
       :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (3,4)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4))
      (SyntheticCategory.biShift_fullyFaithful (3,4)) (tensorLeft_sphere_fullyFaithful 3 4)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).symm (biShift_eq_tensor_Smn 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_pi_four_one_zero
      (z : BiHom 4 3 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply KIP126.ProofTools.Paper.NuNumericalExtensions.sphere_quotient_high_filtration_zero 1 (by decide) 4 3 0 (by decide) z
    exact KIP126.ProofTools.Paper.NuNumericalExtensions.filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 3 4) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 4 3 :=
      (biSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 3 4)).symm ≪≫
        (SyntheticCategory.biShift_comp (3,4) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_pi_four_one_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_tensor_source_square

      (unique:∀u v:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1)
      (d:Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) m w)
      (x:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=
        (susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (3,4)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=KIP126.AdamsSynthetic.Standard.graded_shiftAdditive (3,4)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:T.Faithful:=tensorLeft_sphere_faithful 3 4
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (3,4)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) m w) ≅ Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) :=
      (SyntheticCategory.biShift_comp (m,w) (3,4)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
      ff.preimage (c.hom≫d.hom≫T.map x≫e.inv)
    have hz:F.map z=c.hom≫d.hom≫T.map x≫e.inv:=ff.map_preimage _
    have hzn:z≠0 := by
      intro h
      rw [h,Functor.map_zero] at hz
      have ht:T.map x=0 := by
        apply (cancel_epi (c.hom≫d.hom)).mp
        apply (cancel_mono e.inv).mp
        simpa only [Category.assoc,comp_zero,zero_comp] using hz.symm
      apply hx
      apply T.map_injective
      simpa only [Functor.map_zero] using ht
    have hzx:z=x:=unique z x hzn hx
    rw [hzx] at hz
    have heq:c.inv≫F.map x≫e.hom=d.hom≫T.map x := by
      rw [hz]
      simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
    change d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 3 4 (S_0_0:SyntheticSpectrum),
        κ.hom≫e.hom≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫
          (Standard.quotientAlgebra 1 (by decide)).mul=XModLambdaN.map ν 1 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.quotientAlgebra 1 (by decide)
    obtain ⟨e,he⟩:=q1_unit_tensor_iso
    refine ⟨e,?_⟩
    intro ν
    apply q1_sphere_inclusion_hom_injective
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 1 (by decide)
  obtain ⟨e,he⟩:=q1_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) m w :=
    eqToIso (congrArg (fun p : ℤ×ℤ => Smn (Syn:=SyntheticSpectrum) p.1 p.2)
      (show (m+3,w+4)=(3+m,4+w) by ext <;> dsimp <;> omega)) ≪≫
    ((SyntheticCategory.biShift_comp (3,4) (m,w)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn m w (Smn (Syn:=SyntheticSpectrum) 3 4) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) m w) (Smn (Syn:=SyntheticSpectrum) 3 4)
  have ht:=q1_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 1 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) m w) (Smn (Syn:=SyntheticSpectrum) 3 4)).hom≫
        (quotientClass 1 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 1 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 3 4 m w ν x]
  change homotopyRegrade (add_comm 3 m) (add_comm 4 w)
    (Standard.quotientAlgebraProduct Q (quotientClass 1 ν) x)=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom,eqToIso.hom]
      rw [regrade_precomp,hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]

end NuCrossingAction

private theorem nu_crossing_q1_source_unique
    (a b : BiHom 30 34 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  let E := KIP126.Literature.sphereFirstQuotient model 4 34
  have hane : E a ≠ 0 := by
    intro hz
    exact ha (E.injective (hz.trans E.map_zero.symm))
  have hbne : E b ≠ 0 := by
    intro hz
    exact hb (E.injective (hz.trans E.map_zero.symm))
  rcases NuCrossingCoordinates.a_cases (E a) with hz | hx
  · exact False.elim (hane hz)
  rcases NuCrossingCoordinates.a_cases (E b) with hz | hy
  · exact False.elim (hbne hz)
  exact E.injective (hx.trans hy.symm)

private theorem positive_nu_first_operation_zero_of_action
    (hact : ∀
      (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (_hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
      (z : BiHom 30 34 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)), z ≠ 0 →
      sphereAction (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) z =
        susp_invariance 30 34 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) z ≫
          κ.inv ≫ XModLambdaN.map
            (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) 1)
    (a : BiHom 33 38 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1)) :
    a ≫ XModLambdaN.map positiveNuNormalizedMap 1 = 0 := by
  letI := model.exactness.shiftCommShift (3,4)
  letI := model.exactness.shiftExact (3,4)
  obtain ⟨κ,hκ,_⟩ := quotient_shift_exists model.quotients.coherence (3,4) 1 (S_0_0:SyntheticSpectrum)
  let Q := (model.quotients.functoriality.functor 1).mapIso positiveNuSphereThreeIso
  let E : BiHom 30 34 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≃
      BiHom 33 38 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1) :=
    (susp_invariance 30 34 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).trans
      (Iso.homCongr (Iso.refl _) (κ.symm ≪≫ Q.symm))
  let z := E.symm a
  have ha : E z = a := E.apply_symm_apply a
  have haz : a = shiftHomotopyClass (3,4) (30,34) z ≫ κ.inv ≫
      XModLambdaN.map positiveNuSphereThreeIso.inv 1 := by
    rw [←ha]
    simp [E,Q,Iso.homCongr,susp_invariance,shiftHomotopyClass]
    rfl
  by_cases hz : z = 0
  · rw [haz,hz]
    simp only [shiftHomotopyClass,Functor.map_zero,comp_zero,zero_comp]
  · have hsphere : sphereAction
        (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) z = 0 := by
      apply (KIP126.Literature.sphereFirstQuotient model 5 38).injective
      rw [map_zero]
      have H := KIP126.Literature.Standard.first_quotient_action 1 4 4 34
        (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) z
      change KIP126.Literature.sphereFirstQuotient model 5 38
          (sphereAction (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) z) =
        model.sphereAlgebra.product (1,4) (4,34)
          (KIP126.Literature.sphereFirstQuotient model 1 4
            (quotientClass 1 (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent)))
          (KIP126.Literature.sphereFirstQuotient model 4 34 z) at H
      rw [KIP126.Literature.Standard.nuCofiber_normalized_label] at H
      rw [H]
      rcases NuCrossingCoordinates.a_cases
        (KIP126.Literature.sphereFirstQuotient model 4 34 z) with hy | hy
      · rw [hy]
        exact map_zero _
      · rw [hy]
        exact NuCrossingCoordinates.h2_a_zero
    have haction := hact κ hκ z hz
    have hs : susp_invariance 30 34 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) z ≫
        κ.inv ≫ XModLambdaN.map
          (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) 1 = 0 :=
      haction.symm.trans hsphere
    have hs' := hs
    have hsus : susp_invariance 30 34 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) z =
        shiftHomotopyClass (3,4) (30,34) z := by
      simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
    rw [hsus] at hs'
    rw [normalizedNu_positive_coordinates,model.quotients.functoriality.map_comp,
      model.quotients.functoriality.map_comp] at hs'
    haveI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
      change IsIso ((model.quotients.functoriality.functor 1).map model.nu.unitIso.hom)
      infer_instance
    apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
    simpa only [haz,Category.assoc,zero_comp] using hs'

private theorem positive_nu_first_operation_zero
    (a : BiHom 33 38 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1)) :
    a ≫ XModLambdaN.map positiveNuNormalizedMap 1 = 0 := by
  apply positive_nu_first_operation_zero_of_action
  intro κ hκ z hz
  simpa only [homotopyRegrade] using
    NuCrossingAction.q1_sphere_action_actual_map_general 30 34
      nu_crossing_q1_source_unique κ hκ
      (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) z hz

private theorem essential_extension_impossible_of_high_images
    (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
      (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation (model.convergentMap A B g) p s n x y)
    (hess : TowerEssentialExtension (model.convergentMap A B g) p s n x y)
    (hhigh : ∀ a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower (s+n+1) (a ≫ g)) : False := by
  obtain ⟨_,ar,br,hab,har,hbr⟩ := (tower_extension_iff (model.convergentMap A B g)
    p s n x y).mp he
  have hzero : y = 0 := by
    apply (infinityGradedIso (model.convergence B) p (s+n)).toLinearEquiv.injective
    change (infinityGradedIso (model.convergence B) p (s+n)).hom y =
      (infinityGradedIso (model.convergence B) p (s+n)).hom 0
    rw [←hbr,map_zero]
    apply ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).toAssociatedGraded_eq_zero_iff
      (s+n) p br).mpr
    rw [←hab]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hhigh (((model.syntheticTower.filtration
        (A.obj model.nu model.auxiliary)).F s p).arrow ar)
  exact ((tower_essential_iff_no_zero (model.convergentMap A B g) p s n x y he).mp hess)
    (by rwa [←hzero])

private theorem full_first_kernel_filtration
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = 0) :
    FiltrationAtLeast model.syntheticTower (w-m+1) a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let T := XModLambdaN.cofiberTriangle A 1
  obtain ⟨b,hb⟩ := T.coyoneda_exact₂ (XModLambdaN.cofiberTriangle_distinguished A 1) a ha
  change BiHom m w ((SyntheticCategory.biShift (0,-(1:ℤ))).obj A) at b
  change a = b ≫ lambdaPow 1 A at hb
  have hbottom := shifted_nu_bottom_filtration X (0,-1) m w b
  have hbottom' : FiltrationAtLeast model.syntheticTower (w-m+1) b := by
    convert hbottom using 1
    dsimp
    omega
  have hmap := map_preserves_filtration (model.convergentMap (.shift (0,-1) (.nu X))
    (.nu X) (lambdaPow 1 A)) (m,w) (w-m+1) b hbottom'
  rwa [←hb] at hmap

private theorem finite_nu_no_crossing_of_first_operation_zero
    (hmap : ∀ a : BiHom 33 (37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
      ((SyntheticObject.quotient 1
        (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap)).obj
          model.nu model.auxiliary),
      a ≫ finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 1 = 0) :
    FiniteNoCrossing model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 3 2 3 36 := by
  rintro ⟨a,b,ha,har,hb,x,y,W,hess,_⟩
  have he := KIP126.Literature.Standard.nuCofiber_nu_exponent
  have hl := W.length_lower
  rw [he] at hl
  have ha1 : a = 1 := by omega
  have hb0 : b = 0 := by omega
  subst a
  subst b
  apply essential_extension_impossible_of_high_images
    (.quotient 1 (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap))
    (.quotient 1 (.nu .sphere))
    (finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 1)
    (37-4,37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
    4 1 W.source W.target W.equation hess
  intro c
  rw [hmap c]
  exact Submodule.zero_mem _

private theorem infinite_nu_no_crossing_of_first_operation_zero
    (hmap : ∀ a : BiHom 33 (37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
      ((SyntheticObject.quotient 1
        (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap)).obj
          model.nu model.auxiliary),
      a ≫ finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 1 = 0) :
    InfiniteNoCrossing model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 2 3 36 := by
  rintro ⟨a,b,ha,har,hb,x,y,W,hess,_⟩
  have he := KIP126.Literature.Standard.nuCofiber_nu_exponent
  rw [he] at har hb
  have ha1 : a = 1 := by omega
  have hb0 : b = 0 := by omega
  subst a
  subst b
  apply essential_extension_impossible_of_high_images
    (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap)
    (.nu .sphere) (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map
    (37-4,37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
    4 1 W.source W.target W.equation hess
  intro c
  have hzero : (c ≫ (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map) ≫
      XModLambdaN.incl _ 1 = 0 := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact hmap (c ≫ XModLambdaN.incl _ 1)
  have H := full_first_kernel_filtration .sphere 33
    (37+normalizedExponent model.classicalTower model.auxiliary.nuMap) _ hzero
  convert H using 1 <;> norm_num [SyntheticObject.obj,he]

private theorem actual_nu_first_operation_zero_of_positive
    (hpositive : ∀ a : BiHom 33 38
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1),
      a ≫ XModLambdaN.map positiveNuNormalizedMap 1 = 0) :
    ∀ a : BiHom 33 (37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
      ((SyntheticObject.quotient 1
        (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap)).obj
          model.nu model.auxiliary),
      a ≫ finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 1 = 0 := by
  have transport (e : ℕ) (he : e = 1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ⟶
          model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :
      (∀ a : BiHom 33 38 (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1),
        a ≫ XModLambdaN.map (by simpa only [he,Nat.cast_one] using F) 1 = 0) →
      ∀ a : BiHom 33 (37+e) (XModLambdaN ((SyntheticCategory.biShift (0,(e:ℤ))).obj
          (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) 1),
        a ≫ XModLambdaN.map F 1 = 0 := by
    subst e
    exact id
  exact transport _ KIP126.Literature.Standard.nuCofiber_nu_exponent
    (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map hpositive

private theorem actual_nu_first_operation_zero :
    ∀ a : BiHom 33 (37+normalizedExponent model.classicalTower model.auxiliary.nuMap)
      ((SyntheticObject.quotient 1
        (extensionSourceObject model (.shift 3 .sphere) .sphere model.auxiliary.nuMap)).obj
          model.nu model.auxiliary),
      a ≫ finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 1 = 0 :=
  actual_nu_first_operation_zero_of_positive positive_nu_first_operation_zero

/-- The finite E₃ ν relation has no crossing. Its sole shorter candidate
has zero actual first-quotient ν image, hence cannot be essential. -/
public theorem paper5_13_nu_e3_no_crossing :
    FiniteNoCrossing model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 3 2 3 36 :=
  finite_nu_no_crossing_of_first_operation_zero actual_nu_first_operation_zero

/-- The full ν relation has no crossing. The actual first-quotient zero
image forces every candidate target one filtration higher. -/
public theorem paper5_13_nu_infinite_no_crossing :
    InfiniteNoCrossing model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 2 3 36 :=
  infinite_nu_no_crossing_of_first_operation_zero actual_nu_first_operation_zero

end
end KIP126.ProofTools.Standard
end
