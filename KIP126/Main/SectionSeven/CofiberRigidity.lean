module

public import KIP126.Main.SectionSeven.SphereClasses
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

-- The CSV coordinate calculations use the defining string and list equations.

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison

local notation "M" => standardMilnorCooperations

local notation "L" => sphereClasses

local notation "I" => computationTheorems

section CnuRigidityProof
open CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.Algebra
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}

/-- The actual ν bottom map kills a λν multiple.  In weight 135 the
BHS comparison is the quotient of permanent cycles by B₅, so an E₆
nonzero bottom-cell image cannot detect that zero homotopy class. -/
private theorem target_divisibility_contradiction
    (BHS : EInftyComparison D') (A : NuCofiberNormalization D')
    (T : E2 H SphereSpectrum 14 139)
    (hp : T∈PageRepresentatives.permanentCycles H SphereSpectrum (14,139))
    (hs : SurvivesTo
      (adamsTowerInternalSpectralSequence H.unit (ClassicalObject.nuCofiber.obj D'.hopfAndDetector))
      6 (14,139) (adamsInternalE2Induced H.unit
        (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (14,139) T)) :
    ¬TargetNuDivisible D' T (normalizedNu D' A.nu_exponent) := by
  let negativeZeroIso (k : ℕ) (hk : k=0) (X : Syn) :
      (SyntheticCategory.biShift (0,-(k:ℤ))).obj X ≅ X := by
    subst k
    exact SyntheticCategory.biShift_zero.app X

  have negative_lift_zero_factorization {X Y : Syn} (k : ℕ) (hk : k=0)
      (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj X ⟶ Y)
      (g : X ⟶ Y) (h : lambdaToPositivePow k X ≫ f = g) :
      negativeLift k f ≫ (negativeZeroIso k hk Y).hom = g := by
    subst k
    rw [← h]
    dsimp only [negativeLift, negativeZeroIso, lambdaToPositivePow, lambdaPow]
    simp only [eqToHom_refl, Category.id_comp,
      Iso.app_hom, Category.assoc]
    erw [SyntheticCategory.biShift_zero.hom.naturality]
    rfl

  have normalized_nu_bottom_zero (D' : AdamsComparison H M' Syn)
      (A : KIP126.Literature.AdamsSynthetic.NuCofiberNormalization D') :
      normalizedNu D' A.nu_exponent ≫ D'.nu.unitIso.inv ≫
        D'.nu.functor.map (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) = 0 := by
    have he : (normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.f : ℤ) +
        normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.g +
        normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.h = 1 := by
      change (normalizedExponent H D'.hopfAndDetector.nuMap : ℤ) + _ + _ = 1
      rw [A.nu_exponent,A.bottom_exponent,A.top_exponent]
      norm_num
    have hz := comp_distTriang_mor_zero₁₂ _ (A.triangle he)
    change (D'.normalizedMap (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap).map ≫
      negativeLift (normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.g)
        (D'.normalizedMap .sphere .nuCofiber D'.hopfAndDetector.nuCofiberTriangle.g).map = 0 at hz
    have hb := negative_lift_zero_factorization
      (normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.g) A.bottom_exponent
      (D'.normalizedMap .sphere .nuCofiber D'.hopfAndDetector.nuCofiberTriangle.g).map
      (D'.nu.functor.map D'.hopfAndDetector.nuCofiberTriangle.g)
      (D'.normalizedMap .sphere .nuCofiber D'.hopfAndDetector.nuCofiberTriangle.g).factorization
    have hzero : (D'.normalizedMap (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap).map ≫
        D'.nu.functor.map (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) = 0 := by
      erw [← hb,← Category.assoc,hz,zero_comp]
    dsimp only [normalizedNu]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [hzero,comp_zero]

  have lambda_nu_multiple_bottom_zero (D' : AdamsComparison H M' Syn)
      (A : NuCofiberNormalization D') (a : BiHom 122 132 (S_0_0 : Syn)) :
      sphereProduct (lambdaMultiply 1 (normalizedNu D' A.nu_exponent)) a ≫
        D'.nu.unitIso.inv ≫ D'.nu.functor.map (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) = 0 := by
    let ν := normalizedNu D' A.nu_exponent
    let g := D'.nu.unitIso.inv ≫ D'.nu.functor.map (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap)
    have hz : ν ≫ g = 0 := normalized_nu_bottom_zero D' A
    have hlam : lambdaMultiply 1 ν ≫ g = 0 := by
      dsimp only [lambdaMultiply]
      simp only [Category.assoc]
      rw [hz,comp_zero,comp_zero,comp_zero]
    have hc := D'.sphereProductCommutative 3 3 122 132 (lambdaMultiply 1 ν) a
    norm_num [homotopyRegrade] at hc
    change sphereProduct (lambdaMultiply 1 ν) a ≫ g = 0
    rw [hc]
    dsimp only [sphereProduct]
    simp only [Category.assoc,hlam,comp_zero]

  have classical_permanent_image {X Y : C} (f : X ⟶ Y)
      (p : ℤ × ℤ) (x : E2 H X p.1 p.2)
      (hx : x∈PageRepresentatives.permanentCycles H X p) :
      adamsInternalE2Induced H.unit f p x∈PageRepresentatives.permanentCycles H Y p := by
    obtain ⟨F,hF⟩ := adamsTowerSSDataMorphism_exists H.unit f
    have he (a : E2 H X p.1 p.2) : F.pageMap p 0 a = adamsInternalE2Induced H.unit f p a := by
      apply (adamsTowerSSDataPageIso H.unit Y p.1 p.2 0).toLinearEquiv.injective
      change (adamsTowerSSDataPageIso H.unit Y p.1 p.2 0).hom _ =
        (adamsTowerSSDataPageIso H.unit Y p.1 p.2 0).hom _
      rw [adamsInternalE2Induced_coordinates]
      exact congrArg (fun q => q a) (adamsTowerSSDataMorphism_page_comparison H.unit f F hF p 0)
    obtain ⟨z,hz⟩ := hx
    refine ⟨F.cycleMap p ⊤ z,?_⟩
    have h := F.cycleMap_ofLE_assoc p (show (0:WithTop ℕ)≤⊤ from le_top)
      ((adamsTowerSSData H.unit Y p.1 p.2).pageπ 0)
    rw [← F.pageπ_pageMap] at h
    have hh := congrArg (fun q => q z) h
    change (PageRepresentatives.cycleMap H X ⊤ p ≫ F.pageMap p 0) z =
      (F.cycleMap p ⊤ ≫ PageRepresentatives.cycleMap H Y ⊤ p) z at hh
    change PageRepresentatives.cycleMap H Y ⊤ p (F.cycleMap p ⊤ z) = _
    calc
      _ = F.pageMap p 0 (PageRepresentatives.cycleMap H X ⊤ p z) := hh.symm
      _ = adamsInternalE2Induced H.unit f p x := by rw [hz,he]

  have survives_six_not_boundary_five (X : C) (p : ℤ × ℤ)
      (x : E2 H X p.1 p.2)
      (hx : SurvivesTo (adamsTowerInternalSpectralSequence H.unit X) 6 p x) :
      x∉PageRepresentatives.boundaries H X 5 p := by
    obtain ⟨xr,hrep,hne⟩ := hx
    obtain ⟨hr,z,hz,hzr⟩ := hrep
    rintro ⟨b,hb⟩
    let P := (adamsTowerInternalSpectralSequence H.unit X).ssData p
    change (Subobject.underlying.obj (P.Z 4) : ModuleCat ℤ) at z
    change (Subobject.ofLE (P.Z 4) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) z = x at hz
    change P.pageπ 4 z = xr at hzr
    let bz := (Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4)) b
    have he : (Subobject.ofLE (P.Z 4) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) (z-bz)=0 := by
      rw [map_sub,hz]
      have hbz : (Subobject.ofLE (P.Z 4) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) bz=x := by
        change (Subobject.ofLE (P.B 4) (P.Z 4) _ ≫
          Subobject.ofLE (P.Z 4) (P.Z 0) _ ≫ P.pageπ 0) b = x
        rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
        exact hb
      rw [hbz,sub_self]
    have hm := (subobject_cokernel_π_eq_zero_iff (P.B 0) (P.Z 0) (P.B_le_Z 0)
      ((Subobject.ofLE (P.Z 4) (P.Z 0) (P.Z_anti (by decide))) (z-bz))).mp he
    change (Subobject.ofLE (P.Z 4) (P.Z 0) _ ≫ (P.Z 0).arrow) (z-bz) ∈ _ at hm
    rw [Subobject.ofLE_arrow] at hm
    have hm' := (ModuleCat.subobjectModule P.V).monotone (P.B_mono (by decide : (0:WithTop ℕ)≤4)) hm
    have hb' : (P.Z 4).arrow bz ∈ (ModuleCat.subobjectModule P.V) (P.B 4) := by
      refine ⟨b,?_⟩
      exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.B_le_Z 4)) b).symm
    have hz' := ((ModuleCat.subobjectModule P.V) (P.B 4)).add_mem hm' hb'
    rw [map_sub,sub_add_cancel] at hz'
    apply hne
    rw [← hzr]
    exact (subobject_cokernel_π_eq_zero_iff (P.B 4) (P.Z 4) (P.B_le_Z 4) z).mpr hz'

  have nu_lambda_four_infinity_nonzero
      (BHS : EInftyComparison D') (X : ClassicalObject)
      (x : E2 H (X.obj D'.hopfAndDetector) 14 139)
      (hc : x∈PageRepresentatives.permanentCycles H (X.obj D'.hopfAndDetector) (14,139))
      (hs : SurvivesTo (adamsTowerInternalSpectralSequence H.unit (X.obj D'.hopfAndDetector)) 6 (14,139) x)
      (e : ((D'.family.nu D'.nu (X.obj D'.hopfAndDetector)).sequence.ssData (14,139,135)).eInfty)
      (he : HasInfinityRepresentative (D'.family.nu D'.nu (X.obj D'.hopfAndDetector)) 2 (14,139,135)
        (targetNuLabel D' X 14 139 4 x) e) : e≠0 := by
    have hp := (BHS.labels.2 X (14,139) 4 ⟨x,hc⟩ e).mp he
    intro hz
    rw [hz,map_zero] at hp
    have hb := (NestedQuotient.projection_eq_zero ⟨x,hc⟩).mp hp.symm
    exact survives_six_not_boundary_five (X.obj D'.hopfAndDetector) (14,139) x hs hb

  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i = (D'.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D'.family.functor.map f).toSSDataMorphism
    let PX := (D'.family.functor.obj X).ssData i
    let PY := (D'.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D'.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D'.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D'.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D'.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _
  have family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i ≫ familyPageMap D'.family g r i = familyPageMap D'.family (f ≫ g) r i := by
    rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D'.family.obj X).E₂ i) (e : ((D'.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D'.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D'.family.obj Y) 2 i
        (familyPageMap D'.family f 2 i y) ((D'.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D'.family.functor.obj X).ssData i).Z ⊤)
      (((D'.family.functor.obj X).ssData i).Z 0) _ ≫ ((D'.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D'.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D'.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D'.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])

  have sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k x) = finiteTargetLabel D' .sphere q s t k x := by
    let nx : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj
        (D'.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
      simpa only [ClassicalObject.obj,add_zero] using D'.nuE2 .sphere 0 s t k x
    let f := XModLambdaN.map D'.nu.unitIso.inv q
    have hbase : familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)=
        targetNuLabel D' .sphere s t k x := by
      have hc : familyPageMap D'.family
          (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k) nx =
          D'.sphereE2 s t k x := by
        convert D'.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
      calc
        _ = familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k)
            (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k)
              nx) := congrArg (fun y => familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
        _ = familyPageMap D'.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) ≫ D'.nu.unitIso.inv)
            2 (s,t,t-k) nx :=
          ConcreteCategory.congr_hom (family_page_comp (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
        _ = targetNuLabel D' .sphere s t k x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          dsimp only [targetNuLabel]
          congr 1
    have hlabel : familyPageMap D'.family f 2 (s,t,t-k) (D'.quotientLabel q s t k x)=
        finiteTargetLabel D' .sphere q s t k x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D'.nu.unitIso.inv q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)) :=
          (ConcreteCategory.congr_hom (family_page_comp D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)).symm
        _ = finiteTargetLabel D' .sphere q s t k x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
    exact hlabel

  have detected_map
      (X Y : SyntheticObject) (f : X.obj D'.nu D'.hopfAndDetector ⟶ Y.obj D'.nu D'.hopfAndDetector)
      (i : Tridegree) (x : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (ha : Detects (D'.convergence X) i x a) :
      Detects (D'.convergence Y) i (familyPageMap D'.family f 2 i x) (a≫f) := by
    obtain ⟨c,hca,hce⟩ := D'.comparisonCompatible.convergence_natural X Y f
    obtain ⟨e,he,a',ha',hgr⟩ := ha
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D'.nu) (Y.obj D'.nu D'.hopfAndDetector)
    let m := (i.2.1-i.1,i.2.2)
    let k := (c.filtration_compat i.1 m).choose
    have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
      have hh := (c.filtration_compat i.1 m).choose_spec
      change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
      rw [hca] at hh
      exact hh
    have hc : c.eMap i ≫ ((D'.convergence Y).identification i).hom =
        ((D'.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
      have hh := c.iso_compat i
      simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
    have hq : F.toAssociatedGraded i.1 m ≫
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
        k≫G.toAssociatedGraded i.1 m := by
      exact cokernel.π_desc _ _ _
    refine ⟨(D'.family.functor.map f).eInftyMap i e,family_infinity_representative_map f i x e he,k a',?_,?_⟩
    · have hh := ConcreteCategory.congr_hom hk a'
      change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
      change (F.F i.1 m).arrow a'=a at ha'
      rw [ha'] at hh
      exact hh
    · have hh := ConcreteCategory.congr_hom hc e
      rw [hce] at hh
      change ((D'.convergence Y).identification i).hom ((D'.family.functor.map f).eInftyMap i e)=_
      calc
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (((D'.convergence X).identification i).hom e) := hh
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (F.toAssociatedGraded i.1 m a') := by rw [hgr]
        _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'
  have detects_infinity_equal
      (X : SyntheticObject) (i : Tridegree)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (x y : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (ha : Detects (D'.convergence X) i x a)
      (hb : Detects (D'.convergence X) i y a) :
      ∃ e, HasInfinityRepresentative (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)) 2 i x e ∧
        HasInfinityRepresentative (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)) 2 i y e := by
    obtain ⟨e,he,a',ha',hga⟩ := ha
    obtain ⟨f,hf,b',hb',hgb⟩ := hb
    have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
    have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
    exact ⟨e,he,hef.symm ▸ hf⟩
  have sphere_zero_weight_label_14_139
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 14 139)
      (a : BiHom (139-14) (139-0) (S_0_0 : Syn))
      (ha : Detects D'.sphereConvergence (14,139,139-0) (D'.sphereE2 14 139 0 x) a) :
      D'.sphereFirstQuotient 14 139 (quotientClass 1 a)=x := by
    let y := D'.sphereFirstQuotient 14 139 (quotientClass 1 a)
    have hd := detected_map .sphere (.quotient 1 .sphere)
      (XModLambdaN.incl (S_0_0 : Syn) 1) (14,139,139-0) _ a ha
    have hd' := D'.comparisonCompatible.first_quotient 14 139 y
    have hy : (D'.sphereFirstQuotient 14 139).symm y=quotientClass 1 a := by
      exact (D'.sphereFirstQuotient 14 139).symm_apply_apply _
    rw [hy] at hd'
    obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (14,139,139-0)
      (quotientClass 1 a) _ _ hd hd'
    change HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
      (D'.quotientLabel 1 14 139 0 x) e at he
    change HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
      (D'.quotientLabel 1 14 139 0 y) e at hf
    let g := XModLambdaN.map D'.nu.unitIso.inv 1
    have he' := family_infinity_representative_map g (14,139,139-0) _ _ he
    have hf' := family_infinity_representative_map g (14,139,139-0) _ _ hf
    have hlx := sphere_quotient_label_to_nu 1 0 14 139 x
    have hly := sphere_quotient_label_to_nu 1 0 14 139 y
    change familyPageMap D'.family g 2 (14,139,139-0) (D'.quotientLabel 1 14 139 0 x)=_ at hlx
    change familyPageMap D'.family g 2 (14,139,139-0) (D'.quotientLabel 1 14 139 0 y)=_ at hly
    rw [hlx] at he'
    rw [hly] at hf'
    let xx : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
      ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
    let yy : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
      ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
    have hxq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) xx _).mp he'
    have hyq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) yy _).mp hf'
    have heq := hxq.symm.trans hyq
    change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) xx =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) yy at heq
    have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
    have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
    change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
    have ht : 1+139-(139-0)=1 := by omega
    change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
    rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
    exact (sub_eq_zero.mp hm).symm

  have sphere_to_nu_label (X : ClassicalObject)
      (f : SphereSpectrum ⟶ X.obj D'.hopfAndDetector)
      (x : E2 H SphereSpectrum 14 139) :
      familyPageMap D'.family (D'.nu.unitIso.inv ≫ D'.nu.functor.map f) 2 (14,139,139-(4:ℕ))
        (D'.sphereE2 14 139 4 x) =
      targetNuLabel D' X 14 139 4 (adamsInternalE2Induced H.unit f (14,139) x) := by
    let nx : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj
        (D'.nu.functor.obj SphereSpectrum))).E₂ (14,139,139-(4:ℕ)) := by
      simpa only [ClassicalObject.obj,add_zero] using D'.nuE2 .sphere 0 14 139 4 x
    let ny : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj
        (D'.nu.functor.obj (X.obj D'.hopfAndDetector)))).E₂ (14,139,139-(4:ℕ)) := by
      simpa only [add_zero] using D'.nuE2 X 0 14 139 4 (adamsInternalE2Induced H.unit f (14,139) x)
    have hs : familyPageMap D'.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (14,139,139-(4:ℕ)) nx =
        D'.sphereE2 14 139 4 x := by
      convert D'.comparisonCompatible.sphere_nu 14 139 4 x using 1; simp [nx,ClassicalObject.obj]
    have hn : familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f))
        2 (14,139,139-(4:ℕ)) nx = ny := by
      convert D'.comparisonCompatible.nu_natural .sphere X f 0 14 139 4 x using 1 <;> simp [nx,ny,ClassicalObject.obj]
    rw [← hs]
    have hc := ConcreteCategory.congr_hom
      (family_page_comp
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom)
        (D'.nu.unitIso.inv ≫ D'.nu.functor.map f) 2 (14,139,139-(4:ℕ))) nx
    erw [hc]
    have hm : (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) ≫
        (D'.nu.unitIso.inv ≫ D'.nu.functor.map f) =
        (SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f) ≫
          SyntheticCategory.biShift_zero.hom.app _ := by
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
      exact (SyntheticCategory.biShift_zero.hom.naturality (D'.nu.functor.map f)).symm
    rw [hm]
    erw [← ConcreteCategory.congr_hom (family_page_comp
      ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f))
      (SyntheticCategory.biShift_zero.hom.app _) 2 (14,139,139-(4:ℕ))) nx]
    change familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (14,139,139-(4:ℕ))
      (familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f))
        2 (14,139,139-(4:ℕ)) nx) = _
    rw [hn]
    rfl

  rintro ⟨t,a,hdet,heq⟩
  have hlabel := sphere_zero_weight_label_14_139 BHS T t hdet.1
  have hd := D'.comparisonCompatible.homotopy_lambda 14 139 4 t
  rw [hlabel] at hd
  let bottom := D'.nu.unitIso.inv ≫
    D'.nu.functor.map (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap)
  have hz : lambdaMultiply 4 t ≫ bottom = 0 := by
    rw [← heq]
    exact lambda_nu_multiple_bottom_zero D' A a
  have hm := detected_map .sphere (.nu .nuCofiber) bottom
    (14,139,139-(4:ℕ)) (D'.sphereE2 14 139 4 T) (lambdaMultiply 4 t) hd
  have hl := sphere_to_nu_label .nuCofiber
    (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) T
  change familyPageMap D'.family bottom 2 (14,139,139-(4:ℕ))
    (D'.sphereE2 14 139 4 T) = _ at hl
  erw [hl,hz] at hm
  obtain ⟨e,he,a',ha',hgr⟩ := hm
  have hp' := classical_permanent_image (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap)
    (14,139) T hp
  have hne := nu_lambda_four_infinity_nonzero BHS .nuCofiber _ hp' hs e he
  apply hne
  have ha0 : a'=0 := by
    apply (ModuleCat.mono_iff_injective
      ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
        ((SyntheticObject.nu .nuCofiber).obj D'.nu D'.hopfAndDetector)).F
        14 (139-14,139-(4:ℕ))).arrow).mp inferInstance
    simpa only [map_zero] using ha'
  apply (ModuleCat.mono_iff_injective ((D'.convergence (.nu .nuCofiber)).identification
    (14,139,139-(4:ℕ))).hom).mp inferInstance
  rw [hgr,ha0,map_zero,map_zero]

open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126 KIP126.LinE2 KIP126.Algebra
attribute [local irreducible] KIP126.LinE2.homogeneousPart
variable {L' : SphereAdamsClasses H} {G : TmfDetectionClasses H}
private theorem cnu_target_permanent_context (I' : AdamsComputationTheorems D' L' G) (V : SphereVanishingLine H) :
    IsPermanentCycle (sequence D' .sphere) (14,139) (L'.target M') ∧
    ∃ y : Page D' .nuCofiber 14 139,
      I'.interpretation.coordinateSum .nuCofiber 14 139 [2] = some y ∧
      adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap)
        (14,139) (L'.target M') = y ∧
      SurvivesTo (sequence D' .nuCofiber) 6 (14,139) y := by
  classical
  have t_label (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 14 139 T = I'.interpretation.basis .sphere 14 139 1 := by
    have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      unfold Raw.degrees
      iterate 217 apply List.mem_cons_of_mem
      exact List.mem_cons_self
    have hc := I'.monomials _ hmem rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
    have heq : T=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
      have hs : "1,1,7,1,275,1" ≠ "" := by decide
      have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
        have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
    rw [heq]
    exact he

  have t_permanent_cycle (I' : AdamsComputationTheorems D' L' G) (V : SphereVanishingLine H) :
      IsPermanentCycle (sequence D' .sphere) (14,139) (I'.interpretation.sphere 14 139 T) := by
    let E := sequence D' .sphere
    have h342 : ReachesPage E 1000 (14,139) (I'.interpretation.basis .sphere 14 139 1) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
        unfold Raw.claims
        iterate 342 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 1000 (14,139) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    rw [t_label I']
    apply isPermanentCycle_of_reachesPage E 1000 (by change (2:ℤ)≤1000; omega) (14,139) _ h342
    intro r hr
    haveI : Subsingleton (E.Page r ((14,139)+E.diffDeg r)) := by
      change Subsingleton (E.Page r ((14:ℤ)+r,(139:ℤ)+(r-1)))
      exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r (14+r) (139+(r-1))
        (by decide) (by omega) (V _ _ (by omega) (by omega))
    ext x
    exact Subsingleton.elim _ _

  have hp := t_permanent_cycle I' V
  rw [(distinguished_expression_comparisons I').2.2] at hp
  obtain ⟨x,y,hx,hy,hbottom⟩ := I'.cofiberInclusion ⟨14,139,[1],[2]⟩ (by
    unfold Raw.bottomMaps
    iterate 3 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  have hx' : I'.interpretation.basis .sphere 14 139 1 = x := by
    simpa only [E2Interpretation.coordinateSum, vx, if_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Option.some.injEq] using hx
  have ht : L'.target M' = x :=
    (distinguished_expression_comparisons I').2.2.symm.trans ((t_label I').trans hx')
  obtain ⟨y',hy',hs,_⟩ := cnu_target_through5 I'
  have he : y=y' := Option.some.inj (hy.symm.trans hy')
  refine ⟨hp,y,hy,?_,he.symm ▸ hs⟩
  exact (congrArg (adamsInternalE2Induced H.unit
    (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (14,139)) ht).trans hbottom

end CnuRigidityProof

/-- The last rigidity step of `prop:state5false`. The cofiber is the
actual cofiber of D.hopfAndDetector.nuMap, and [2] is the same bottom-cell
image as in I.cofiberInclusion. The exponent four gives incoming pages 2..5,
not a permanence claim about the cofiber class. -/
theorem target_divisibility_forces_cnu_incoming
    (hdiv : TargetNuDivisible D ((L).target M) h2) :
    ∃ y : KIP126.Computation.SphereAndCofiber.Page D .nuCofiber 14 139,
      (I).interpretation.coordinateSum .nuCofiber 14 139 [2] = some y ∧
      ∃ r : ℤ, 2 ≤ r ∧ r ≤ 5 ∧
        HitOnPage (KIP126.Computation.SphereAndCofiber.sequence D .nuCofiber) r (14,139) y := by
  obtain ⟨hp, y, _, hbottom, hs⟩ := cnu_target_permanent_context I sphereVanishing
  apply False.elim
  apply target_divisibility_contradiction literatureTheorems.synthetic.eInfty
    literatureTheorems.applicability.nuCofiber ((L).target M) hp _ hdiv
  exact hbottom.symm ▸ hs

end
end KIP126.Main.SectionSeven
