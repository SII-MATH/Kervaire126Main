module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Main.Computation.Lambda


@[expose] public section

namespace KIP126.Main.SectionSeven.DifferentialCriterion
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.SphereAndCofiber
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem eta_detection_family_map_data {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
  have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
  have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
      (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _


private theorem eta_detection_family_page_comp {D : AdamsComparison H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [eta_detection_family_map_data,eta_detection_family_map_data,eta_detection_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem eta_detection_family_infinity_representative_map {D : AdamsComparison H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [eta_detection_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem eta_detection_sphere_quotient_label_to_nu {D : AdamsComparison H M Syn} (q k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x) = finiteTargetLabel D .sphere q s t k x := by
  classical
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let f := XModLambdaN.map D.nu.unitIso.inv q
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (eta_detection_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (eta_detection_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (eta_detection_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem eta_detection_detected_map {D : AdamsComparison H M Syn}
    (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
    (i : Tridegree) (x : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (ha : Detects (D.convergence X) i x a) :
    Detects (D.convergence Y) i (familyPageMap D.family f 2 i x) (a≫f) := by
  classical
  obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural X Y f
  obtain ⟨e,he,a',ha',hgr⟩ := ha
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.hopfAndDetector)
  let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.hopfAndDetector)
  let m := (i.2.1-i.1,i.2.2)
  let k := (c.filtration_compat i.1 m).choose
  have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
    have hh := (c.filtration_compat i.1 m).choose_spec
    change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
    rw [hca] at hh
    exact hh
  have hc : c.eMap i ≫ ((D.convergence Y).identification i).hom =
      ((D.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
    have hh := c.iso_compat i
    simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
  have hq : F.toAssociatedGraded i.1 m ≫
      Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
      k≫G.toAssociatedGraded i.1 m := by
    exact cokernel.π_desc _ _ _
  refine ⟨(D.family.functor.map f).eInftyMap i e,eta_detection_family_infinity_representative_map f i x e he,k a',?_,?_⟩
  · have hh := ConcreteCategory.congr_hom hk a'
    change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
    change (F.F i.1 m).arrow a'=a at ha'
    rw [ha'] at hh
    exact hh
  · have hh := ConcreteCategory.congr_hom hc e
    rw [hce] at hh
    change ((D.convergence Y).identification i).hom ((D.family.functor.map f).eInftyMap i e)=_
    calc
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (((D.convergence X).identification i).hom e) := hh
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (F.toAssociatedGraded i.1 m a') := by rw [hgr]
      _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'


private theorem eta_detection_detects_infinity_equal {D : AdamsComparison H M Syn}
    (X : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (x y : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (ha : Detects (D.convergence X) i x a)
    (hb : Detects (D.convergence X) i y a) :
    ∃ e, HasInfinityRepresentative (D.family.obj (X.obj D.nu D.hopfAndDetector)) 2 i x e ∧
      HasInfinityRepresentative (D.family.obj (X.obj D.nu D.hopfAndDetector)) 2 i y e := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
  have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
  exact ⟨e,he,hef.symm ▸ hf⟩


private theorem eta_detection_sphere_zero_weight_label_10_134 {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) (134-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (10,134,134-0) (D.sphereE2 10 134 0 x) a) :
    D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 10 134 (quotientClass 1 a)
  have hd := eta_detection_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (10,134,134-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 10 134 y
  have hy : (D.sphereFirstQuotient 10 134).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 10 134).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := eta_detection_detects_infinity_equal (.quotient 1 .sphere) (10,134,134-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := eta_detection_family_infinity_representative_map g (10,134,134-0) _ _ he
  have hf' := eta_detection_family_infinity_representative_map g (10,134,134-0) _ _ hf
  have hlx := eta_detection_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 x
  have hly := eta_detection_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 y
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 x)=_ at hlx
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  have hxq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) yy _).mp hf'
  have heq := hxq.symm.trans hyq
  change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) xx =
    NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) yy at heq
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
  have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  have ht : 1+134-(134-0)=1 := by omega
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


omit [HasFunctorialCofiber (C := Syn)] in
private theorem eta_detection_shift_assoc_inv (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private def eta_detection_push3 {m w : ℤ} {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-3) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-3)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-3)).map a ≫ f


private theorem eta_detection_eta_push3 (D : AdamsComparison H M Syn) {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : Syn)) (x : BiHom 124 134 X) :
    sphereAction ν (eta_detection_push3 f x) = eta_detection_push3 f (sphereAction ν x) := by
  classical
  have ha := eta_detection_shift_assoc_inv D.shiftCoherence (1,2) (124,134) (0,-3)
    (125,136) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  simp only [eta_detection_push3, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,131)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (124,131)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-3)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-3)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem eta_detection_eta_lambda3_right (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (u : BiHom 124 134 (S_0_0 : Syn)) :
    sphereProduct η (lambdaMultiply 3 u)=lambdaMultiply 3 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : Syn)) :
      eta_detection_push3 (lambdaPow 3 (S_0_0 : Syn)) a=lambdaMultiply 3 a := by
    simp only [eta_detection_push3,lambdaMultiply]
    erw [lambdaPow_naturality]
    rfl
  have h := eta_detection_eta_push3 D (lambdaPow 3 (S_0_0 : Syn)) η u
  rw [heq,heq] at h
  exact h


private def eta_detection_push6 {m w : ℤ} {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-6) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-6)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-6)).map a ≫ f


private theorem eta_detection_eta_push6 (D : AdamsComparison H M Syn) {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : Syn)) (x : BiHom 124 134 X) :
    sphereAction ν (eta_detection_push6 f x) = eta_detection_push6 f (sphereAction ν x) := by
  classical
  have ha := eta_detection_shift_assoc_inv D.shiftCoherence (1,2) (124,134) (0,-6)
    (125,136) (124,128) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  simp only [eta_detection_push6, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,128)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (124,128)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-6)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-6)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-6)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem eta_detection_eta_lambda6_right (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (u : BiHom 124 134 (S_0_0 : Syn)) :
    sphereProduct η (lambdaMultiply 6 u)=lambdaMultiply 6 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : Syn)) :
      eta_detection_push6 (lambdaPow 6 (S_0_0 : Syn)) a=lambdaMultiply 6 a := by
    simp only [eta_detection_push6,lambdaMultiply]
    erw [lambdaPow_naturality]
    rfl
  have h := eta_detection_eta_push6 D (lambdaPow 6 (S_0_0 : Syn)) η u
  rw [heq,heq] at h
  exact h


private theorem eta_detection_lambda_three_3_136 (D : AdamsComparison H M Syn)
    (c : BiHom 125 136 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 3 c)=lambdaMultiply 6 c := by
  classical
  have ha := eta_detection_shift_assoc_inv D.shiftCoherence (125,136) (0,-3) (0,-3)
    (125,133) (0,-6) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 3 (Smn 125 136)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 3 3 6 (by decide) (Smn 125 136)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem eta_detection_lambda_three_7_140 (D : AdamsComparison H M Syn)
    (c : BiHom 125 140 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 7 c)=lambdaMultiply 10 c := by
  classical
  have ha := eta_detection_shift_assoc_inv D.shiftCoherence (125,140) (0,-7) (0,-3)
    (125,133) (0,-10) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,140) (0,-7)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 7 (Smn 125 140)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 7 3 10 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem eta_detection_lambda_three_6_139 (D : AdamsComparison H M Syn)
    (c : BiHom 125 139 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 6 c)=lambdaMultiply 9 c := by
  classical
  have ha := eta_detection_shift_assoc_inv D.shiftCoherence (125,139) (0,-6) (0,-3)
    (125,133) (0,-9) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,139) (0,-6)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 6 (Smn 125 139)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 6 3 9 (by decide) (Smn 125 139)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,eqToIso.inv,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem eta_detection_vanishes_mod_lambda_iff_multiple
    (n : ℕ) {X : Syn} (m w : ℤ) (z : BiHom m (w-(n:ℤ)) X) :
    VanishesModLambda n z ↔ ∃ b : BiHom m w X, lambdaMultiply n b=z := by
  classical
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(n:ℤ))
  let e : F.obj (Smn m w : Syn) ≅ Smn m (w-(n:ℤ)) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  have he (b : BiHom m w X) : lambdaMultiply n b=e.inv≫F.map b≫lambdaPow n X := by
    have he' : lambdaMultiply n b=e.inv≫lambdaPow n (Smn m w)≫b := by
      unfold lambdaMultiply
      change eqToHom (by congr 1; simp) ≫
        (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0 ≫
        lambdaPow n (Smn m w) ≫ b =
        (eqToHom (by congr 1; simp) ≫
          (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0) ≫
        lambdaPow n (Smn m w) ≫ b
      exact (Category.assoc _ _ _).symm
    rw [he',←lambdaPow_naturality n b]
  constructor
  · intro hz
    obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors n z).mp hz
    let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).preimage (e.hom≫a)
    have hb : F.map b=e.hom≫a :=
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).map_preimage _
    refine ⟨b,?_⟩
    rw [he,hb]
    simp only [Category.assoc,e.inv_hom_id_assoc]
    exact ha
  · rintro ⟨b,rfl⟩
    apply (vanishesModLambda_iff_factors n (lambdaMultiply n b)).mpr
    exact ⟨e.inv≫F.map b,by rw [Category.assoc,←he]⟩


private theorem eta_detection_map_filtration {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
    (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
  classical
  obtain ⟨z,hz⟩ := hx
  refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
  change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
    adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
  rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
  rfl


private theorem eta_detection_lambda_9_iff_filtration_14 {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (a : BiHom 125 130 (S_0_0 : Syn)) :
    VanishesModLambda 9 a ↔ FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
  classical
  have h := BHS.filtration_lambda .sphere 125 130 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 139 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 9 b=a ≫ D.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (eta_detection_vanishes_mod_lambda_iff_multiple 9 125 139 a).mp hz
    have haν := h.mpr ⟨b ≫ D.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ D.nu.unitIso.inv) hb)⟩
    have hm := eta_detection_map_filtration (D:=D) D.nu.unitIso.hom (a ≫ D.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (eta_detection_map_filtration (D:=D) D.nu.unitIso.inv a ha)
    apply (eta_detection_vanishes_mod_lambda_iff_multiple 9 125 139 a).mpr
    refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ D.nu.unitIso.hom) hb


private theorem eta_detection_lambda_10_iff_filtration_15 {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (a : BiHom 125 130 (S_0_0 : Syn)) :
    VanishesModLambda 10 a ↔ FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a := by
  classical
  have h := BHS.filtration_lambda .sphere 125 130 15 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (eta_detection_vanishes_mod_lambda_iff_multiple 10 125 140 a).mp hz
    have haν := h.mpr ⟨b ≫ D.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ D.nu.unitIso.inv) hb)⟩
    have hm := eta_detection_map_filtration (D:=D) D.nu.unitIso.hom (a ≫ D.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (eta_detection_map_filtration (D:=D) D.nu.unitIso.inv a ha)
    apply (eta_detection_vanishes_mod_lambda_iff_multiple 10 125 140 a).mpr
    refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ D.nu.unitIso.hom) hb


private theorem eta_detection_theta_quotient_frame {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) z
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



private theorem eta_detection_theta_sphere_frame {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  have eta_detection_family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
      familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
    have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
    have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
        (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _
  have map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [eta_detection_family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  obtain ⟨x',hx',hframe⟩ := eta_detection_theta_quotient_frame I s t k hst hsk x hx
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [eta_detection_family_map_data,eta_detection_family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [eta_detection_family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh


private theorem eta_detection_theta_detection_step {D : AdamsComparison H M Syn}
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := (D.sphereConvergence.identification i).inv q
  have he : (D.sphereConvergence.identification i).hom e=q :=
    ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (subobject_cokernel_π_eq_zero_iff
      (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
      (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
    rw [ha'] at hmem
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩

private theorem eta_detection_stem124_weight128_filtration11_branches {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (x13 : E2 H SphereSpectrum 13 137)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha11 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a) :
    SphereDetected D 13 137 9 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 10 b=a := by
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
      11 13 124 128 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-128) (j,124+j)) :=
      permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 128 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have ha13 := hgap ha11
  have hf13 := eta_detection_theta_sphere_frame I BHS 13 137 9 (by omega) (by omega) x13 h13
  rcases eta_detection_theta_detection_step (13,137,128) (D.sphereE2 13 137 9 x13) hf13 a ha13 with hdet|ha14
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
  have h := BHS.filtration_lambda .sphere 124 128 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb

private theorem eta_detection_eta_weight128_branches_filtration_fifteen {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (b : BiHom 124 128 (S_0_0 : Syn))
    (hbranch : SphereDetected D 13 137 9 (I.interpretation.sphere 13 137 correction)
        b ∨
      ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=b) :
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
    have hd := D.multiplicationCompatible 1 2 13 137 0 9
      (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)
      η b hηd h13.1
    change Detects D.sphereConvergence (14,139,130)
      (D.sphereE2 14 139 9 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
        (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)))
      (sphereProduct η b) at hd
    rw [hp,map_zero] at hd
    exact detects_zero_filtration D.sphereConvergence (14,139,130) hd
  · have had := D.comparisonCompatible.homotopy_lambda 14 138 10 a
    rw [ha] at had
    have hd := D.multiplicationCompatible 1 2 14 138 0 10
      (Sphere.Internal.hi H M 1) (D.sphereFirstQuotient 14 138 (quotientClass 1 a))
      η b hηd had
    change Detects D.sphereConvergence (15,140,130) _ (sphereProduct η b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)).arrow a'∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,130)))
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

private theorem eta_detection_eta_weight128_filtration_eleven {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (SF : Derived.SphereFacts I.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I.interpretation.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η a) := by
  exact eta_detection_eta_weight128_branches_filtration_fifteen I SF η hη a
    (eta_detection_stem124_weight128_filtration11_branches I BHS _ h13
      SF.e5_stem124_af11 SF.e4_stem124_af12 a ha)

private theorem eta_detection_theta_u_eta_filtration_error {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (SF : Derived.SphereFacts I.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I.interpretation.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toAdamsComparisonData L u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
      ((show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (sphereProduct θ θ)) -
        (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 (lambdaMultiply 3 (sphereProduct η u)))) := by
  have hfirst := eta_detection_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) u hu.1
  have hu6 := D.comparisonCompatible.homotopy_lambda 10 134 6 u
  rw [hfirst] at hu6
  have hdelta := detects_sub_filtration D.sphereConvergence (10,134,128) hc4.1 hu6
  have heta := eta_detection_eta_weight128_filtration_eleven I BHS SF h13 η hη _ hdelta
  have he : sphereProduct η ((show BiHom 124 128 (S_0_0 : Syn) from sphereProduct θ θ)-(show BiHom 124 128 (S_0_0 : Syn) from lambdaMultiply 6 u))=
      (show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (sphereProduct θ θ))-(show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (lambdaMultiply 6 u)) := by
    simp only [sphereProduct,Preadditive.comp_sub,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat]
  rw [he,eta_detection_eta_lambda6_right D η u,←eta_detection_lambda_three_3_136 D (sphereProduct η u)] at heta
  exact heta

private theorem eta_detection_lambda_three_preserves_filtration_fifteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (a : BiHom 125 133 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (lambdaMultiply 3 a) := by
  have h := BHS.filtration_lambda .sphere 125 133 15 (by omega) (a≫D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a≫D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum),lambdaMultiply 7 b=a≫D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (eta_detection_map_filtration (D:=D) D.nu.unitIso.inv a ha)
  let c : BiHom 125 140 (S_0_0 : Syn) := b≫D.nu.unitIso.hom
  have hc : lambdaMultiply 7 c=a := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z≫D.nu.unitIso.hom) hb
  apply (eta_detection_lambda_10_iff_filtration_15 BHS _).mp
  apply (eta_detection_vanishes_mod_lambda_iff_multiple 10 125 140 _).mpr
  exact ⟨c,by rw [←hc,eta_detection_lambda_three_7_140 D c]⟩

private theorem eta_detection_sphere_first_label_transport {D : AdamsComparison H M Syn} (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    D.sphereFirstQuotient s t
      (firstLabel D .sphere s t x ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom) 1)=x := by
  let e : nuZero D .sphere ≅ (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ D.nu.unitIso
  let q := (D.quotientFunctoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
      E2 H SphereSpectrum s t) (Int.add_zero t)) (D.firstQuotient SphereSpectrum 0 s t)
  change c ((firstLabel D .sphere s t x ≫ q.hom) ≫ q.inv)=x
  rw [Category.assoc,q.hom_inv_id]
  erw [Category.comp_id]
  have cast_symm (w₁ w₂ : ℤ) (h : w₁=w₂)
      (E : BiHom (t-s) w₁ (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t)
      (x : E2 H SphereSpectrum s t) :
      Eq.mp (congrArg (fun z => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1)) h) (E.symm x) =
        (Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
          E2 H SphereSpectrum s t) h) E).symm x := by
    subst w₂
    rfl
  have hx : firstLabel D .sphere s t x=c.symm x := by
    dsimp only [firstLabel,c,ClassicalObject.obj,nuZero]
    exact cast_symm (t+0) t (Int.add_zero t) (D.firstQuotient SphereSpectrum 0 s t) x
  rw [hx,c.apply_symm_apply]

private theorem eta_detection_sphere_permanent_first_quotient_lift {D : AdamsComparison H M Syn}
    (synthetic : SyntheticComparisonTheorems D) (s t : ℤ) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn), D.sphereFirstQuotient s t (quotientClass 1 a)=x := by
  have hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := by
    exact hx
  obtain ⟨a,ha⟩ := (synthetic.permanent_lift .sphere s t x).mp hp
  let e := SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  refine ⟨a≫e,?_⟩
  have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
    unfold quotientClass
    simp only [Category.assoc]
    exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
  rw [hc,ha]
  exact eta_detection_sphere_first_label_transport s t x

private theorem eta_detection_detects_of_difference_in_next_filtration
    {H' : Syn} {unit : S_0_0 ⟶ H'} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : FiltrationAtLeast unit (i.1+1) (b-a)) :
    Detects c i x b := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let P := towerFiltration unit X
  let p := (i.2.1-i.1,i.2.2)
  have hmem : b-a∈(ModuleCat.subobjectModule (syntheticHomotopy X p)) (P.F (i.1+1) p) := by
    simpa only [P,p,FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using hb
  obtain ⟨z,hz⟩ := hmem
  let j := Subobject.ofLE (P.F (i.1+1) p) (P.F i.1 p) (P.mono i.1 p)
  refine ⟨e,he,a'+j z,?_,?_⟩
  · rw [map_add]
    have hj : (P.F i.1 p).arrow (j z)=(P.F (i.1+1) p).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.mono i.1 p)) z
    rw [hj,ha',hz]
    abel
  · rw [map_add]
    have hj : P.toAssociatedGraded i.1 p (j z)=0 :=
      ConcreteCategory.congr_hom (cokernel.condition j) z
    rw [hj,add_zero]
    exact hga

private theorem eta_detection_target_detection_lambda_three {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (x : E2 H SphereSpectrum 14 139)
    (hx : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (c : BiHom 125 133 (S_0_0 : Syn))
    (hc : Detects D.sphereConvergence (14,139,133) (D.sphereE2 14 139 6 x) c) :
    Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 x) (lambdaMultiply 3 c) := by
  obtain ⟨t,ht⟩ := eta_detection_sphere_permanent_first_quotient_lift BHS 14 139 x hx
  have ht6 := D.comparisonCompatible.homotopy_lambda 14 139 6 t
  rw [ht] at ht6
  have hdiff := detects_sub_filtration D.sphereConvergence (14,139,133) hc ht6
  have hdiff3 := eta_detection_lambda_three_preserves_filtration_fifteen BHS _ hdiff
  have hlin : lambdaMultiply 3 (c-(show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 t))=
      (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 c)-
      (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 (lambdaMultiply 6 t)) := by
    simp only [lambdaMultiply,Preadditive.comp_sub,Nat.cast_ofNat,Int.reduceSub]
  rw [hlin,eta_detection_lambda_three_6_139 D t] at hdiff3
  have ht9 := D.comparisonCompatible.homotopy_lambda 14 139 9 t
  rw [ht] at ht9
  exact eta_detection_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) ht9 hdiff3

private theorem eta_detection_square_detection_eta_detection_eta_target_detected {D : AdamsComparison H M Syn}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (SF : Derived.SphereFacts I.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I.interpretation.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toAdamsComparisonData L u)
    (hc5 : EtaExtensionDetectionAt M D.toAdamsComparisonData L η u) :
    Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M))
      (sphereProduct η (sphereProduct θ θ)) := by
  have hp := SF.t_permanent_cycle
  rw [(distinguished_expression_comparisons I).2.2] at hp
  have hlow := eta_detection_target_detection_lambda_three BHS (L.target M) hp _ hc5
  exact eta_detection_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) hlow
    (eta_detection_theta_u_eta_filtration_error I BHS SF h13 η hη θ hc4 u hu)

private theorem eta_detection_survives_twelve_not_boundary_eleven (X : C) (p : ℤ × ℤ)
    (x : E2 H X p.1 p.2)
    (hx : SurvivesTo (adamsTowerInternalSpectralSequence H.unit X) 12 p x) :
    x∉PageRepresentatives.boundaries H X 11 p := by
  obtain ⟨xr,hrep,hne⟩ := hx
  obtain ⟨hr,z,hz,hzr⟩ := hrep
  rintro ⟨b,hb⟩
  let P := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  change (Subobject.underlying.obj (P.Z 10) : ModuleCat ℤ) at z
  change (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) z = x at hz
  change P.pageπ 10 z = xr at hzr
  let bz := (Subobject.ofLE (P.B 10) (P.Z 10) (P.B_le_Z 10)) b
  have he : (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) (z-bz)=0 := by
    rw [map_sub,hz]
    have hbz : (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) bz=x := by
      change (Subobject.ofLE (P.B 10) (P.Z 10) _ ≫
        Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ P.pageπ 0) b = x
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hb
    rw [hbz,sub_self]
  have hm := (subobject_cokernel_π_eq_zero_iff (P.B 0) (P.Z 0) (P.B_le_Z 0)
    ((Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide))) (z-bz))).mp he
  change (Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ (P.Z 0).arrow) (z-bz) ∈ _ at hm
  rw [Subobject.ofLE_arrow] at hm
  have hm' := (ModuleCat.subobjectModule P.V).monotone (P.B_mono (by decide : (0:WithTop ℕ)≤10)) hm
  have hb' : (P.Z 10).arrow bz ∈ (ModuleCat.subobjectModule P.V) (P.B 10) := by
    refine ⟨b,?_⟩
    exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.B_le_Z 10)) b).symm
  have hz' := ((ModuleCat.subobjectModule P.V) (P.B 10)).add_mem hm' hb'
  rw [map_sub,sub_add_cancel] at hz'
  apply hne
  rw [← hzr]
  exact (subobject_cokernel_π_eq_zero_iff (P.B 10) (P.Z 10) (P.B_le_Z 10) z).mpr hz'

private theorem eta_detection_sphere_label_to_nu {D : AdamsComparison H M Syn} (s t : ℤ) (k : ℕ) (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (eta_detection_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  exact hbase

private theorem eta_detection_sphere_target_nine_nonzero_of_survives_twelve {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 14 139)
    (hp : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (hs : SurvivesTo (sequence D .sphere) 12 (14,139) x)
    (e : ((D.family.sphere).sequence.ssData (14,139,130)).eInfty)
    (he : HasInfinityRepresentative D.family.sphere 2 (14,139,130)
      (D.sphereE2 14 139 9 x) e) : e≠0 := by
  have hn := eta_detection_family_infinity_representative_map D.nu.unitIso.inv (14,139,130) _ _ he
  have hl := eta_detection_sphere_label_to_nu (D:=D) 14 139 9 x
  change familyPageMap D.family D.nu.unitIso.inv 2 (14,139,130) (D.sphereE2 14 139 9 x)=_ at hl
  rw [hl] at hn
  have hf := (BHS.labels.2 .sphere (14,139) 9 ⟨x,hp⟩ _).mp hn
  intro hz
  rw [hz,map_zero,map_zero] at hf
  have hb := (NestedQuotient.projection_eq_zero ⟨x,hp⟩).mp hf.symm
  exact eta_detection_survives_twelve_not_boundary_eleven SphereSpectrum (14,139) x hs
    (PageRepresentatives.boundaries_monotone H SphereSpectrum (14,139) (by decide : (10:ℤ)≤11) hb)

private theorem eta_detection_target_detected_not_filtration_fifteen {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 14 139)
    (hp : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (hs : SurvivesTo (sequence D .sphere) 12 (14,139) x)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 x) a) :
    ¬FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a := by
  intro hf
  have hz : Detects D.sphereConvergence (14,139,130) 0 0 :=
    ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,0,map_zero _,by simp only [map_zero]⟩
  have hza : Detects D.sphereConvergence (14,139,130) 0 a :=
    eta_detection_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) hz
      (by simpa only [sub_zero,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hf)
  obtain ⟨e,he,he0⟩ := eta_detection_detects_infinity_equal .sphere (14,139,130) a _ 0 ha hza
  exact eta_detection_sphere_target_nine_nonzero_of_survives_twelve BHS x hp hs e he
    (he0.unique (HasInfinityRepresentative.zero _ 2 (by decide) _))

private theorem eta_detection_finite_sphere_infinity_nonzero {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e) : e≠0 := by
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hh := eta_detection_family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := eta_detection_sphere_quotient_label_to_nu (D:=D) q 0 s t x
  change familyPageMap D.family g 2 (s,t,t-0) (D.quotientLabel q s t 0 x)=_ at hl
  rw [hl] at hh
  let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  have hp := (BHS.labels.1 .sphere q hq (s,t) 0 hq y _).mp hh
  intro he0
  rw [he0,map_zero,map_zero] at hp
  have hm := (NestedQuotient.projection_eq_zero y).mp hp.symm
  have hb : (1:ℤ)+t-(t-0)=1 := by omega
  change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
  rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact hne hm

private theorem eta_detection_sphere_zero_weight_nonzero_detection_u {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) 134 (S_0_0 : Syn))
    (ha : D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x) (hne : x≠0) :
    SphereDetected D 10 134 0 x a := by
  have h0 : lambdaMultiply 0 a=a := by
    have hc := D.shiftCoherence.right_unit (134-10,134) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (134-10,134) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn (134-10) 134 : Syn) := by
      change (biShiftAddIso (134-10,134) (0,0) (134-10,134) (by simp)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (134-10,134) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (134-10,134) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hd := D.comparisonCompatible.homotopy_lambda 10 134 0 a
  rw [h0,ha] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩ := hd
  refine ⟨e,he,?_⟩
  let f := XModLambdaN.incl (S_0_0 : Syn) 1
  have hf := eta_detection_family_infinity_representative_map f (10,134,134-0) _ _ he
  have hcycle : x∈PageRepresentatives.cycles H SphereSpectrum 1 (10,134) := by
    rw [PageRepresentatives.cycles_one]
    exact Submodule.mem_top
  have hfn := eta_detection_finite_sphere_infinity_nonzero BHS 1 (by decide) 10 134 x hcycle hne _ hf
  intro hz
  apply hfn
  rw [hz,map_zero]

private theorem eta_detection_u_choice_exists {D : AdamsComparison H M Syn} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (SF : Derived.SphereFacts I.interpretation) : ∃u,UChoice M D.toAdamsComparisonData L u := by
  have hp := SF.u_permanent
  change NonzeroSurvival (sequence D .sphere) (10,134) (I.interpretation.sphere 10 134 U) at hp
  rw [(distinguished_expression_comparisons I).2.1] at hp
  obtain ⟨z,hz,hzn⟩ := hp
  have hcycle : IsPermanentCycle (sequence D .sphere) (10,134) (L.U M) := ⟨z,hz⟩
  have hn : L.U M≠0 := by
    intro h0
    let P := (sequence D .sphere).ssData (10,134)
    have hz0 : (Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0) z=L.U M := hz
    have hh := P.infinity_projection_eq_of_page_projection_eq 0 z 0
      (by simpa only [map_zero] using hz0.trans h0)
    exact hzn (by simpa only [map_zero] using hh)
  obtain ⟨u,hu⟩ := eta_detection_sphere_permanent_first_quotient_lift BHS 10 134 (L.U M) hcycle
  exact ⟨u,eta_detection_sphere_zero_weight_nonzero_detection_u BHS.eInfty (L.U M) u hu hn⟩

private theorem eta_detection_permanent_quotient_frame_of_page_six {D : AdamsComparison H M Syn}
    (s t : ℤ) (k : ℕ) (hk : 4≤k) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (sequence D .sphere) (s,t) x)
    (a : (sequence D .sphere).Page 6 (s,t))
    (ha : RepresentsOnPage (sequence D .sphere) 6 (s,t) x a)
    (hall : ∀ y : (sequence D .sphere).Page 6 (s,t),y=0∨y=a) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t),x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0∨q=NestedQuotient.projection _ _ x' := by
  let E := sequence D .sphere
  let P := E.ssData (s,t)
  obtain ⟨z,hz⟩ := hx
  change (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ) at z
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  let incl := Subobject.ofLE (P.Z ⊤) (P.Z 4) (P.Z_anti le_top)
  let val (q : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ)) := P.pageπ 4 (incl q)
  have rep : RepresentsOnPage E 6 (s,t) x (val z) := by
    refine ⟨by decide,incl z,?_,rfl⟩
    change PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) (incl z)=x
    exact (ConcreteCategory.congr_hom
      (PageRepresentatives.cycleMap_factor H SphereSpectrum (s,t) 4 ⊤ le_top) z).trans hz
  have hvz : val z=a := represents_unique (E:=E) (r:=6) (p:=(s,t)) (x:=x) rep ha
  have zero_of_page_zero (q : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hq : val q=0) : PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) q ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4)) (incl q)).mp hq
    have h5 : PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) q ∈
        PageRepresentatives.boundaries H SphereSpectrum 5 (s,t) := by
      refine ⟨b,?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s,t) b=_
      have hfactor : Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t)=
          PageRepresentatives.boundaryMap H SphereSpectrum 4 (s,t) := by
        dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object]
        rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      rw [←hfactor,CategoryTheory.comp_apply]
      change PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) ((Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4)) b)=_
      exact (congrArg (fun w => PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) w) hb).trans (ConcreteCategory.congr_hom
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s,t) 4 ⊤ le_top) q)
    exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s,t) (by omega : (5:ℤ)≤1+k) h5
  refine ⟨x',rfl,?_⟩
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  change (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ) at z'
  rcases hall (val z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_page_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y-NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x∈_
    rw [←hz',←hz,←map_sub]
    exact zero_of_page_zero (z'-z) (by
      change P.pageπ 4 (incl (z'-z))=0
      rw [map_sub,map_sub]
      change val z'-val z=0
      rw [h1,hvz,sub_self])

private theorem eta_detection_sphere_frame_of_permanent_quotient {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D)
    (s t : ℤ) (k : ℕ)
    (x : E2 H SphereSpectrum s t)
    (hq : ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t),x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0∨q=NestedQuotient.projection _ _ x') :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
      familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
    have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
    have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
        (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _
  have map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  obtain ⟨x',hx',hframe⟩ := hq
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [family_map_data,family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh

private theorem eta_detection_target_infinity_frame
    {I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G} (BHS : SyntheticComparisonTheorems D)
    (SF : Derived.SphereFacts I.interpretation)
    (hframe6 : (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) (k : ℕ) (hk : 4≤k) :
    ∀ e : ((D.family.sphere).sequence.ssData (14,139,139-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (14,139,139-k)
        (D.sphereE2 14 139 k (L.target M)) e := by
  obtain ⟨⟨a,ha,hall⟩,_⟩ := hframe6
  have hp := SF.t_permanent_cycle
  rw [(distinguished_expression_comparisons I).2.2] at hp
  exact eta_detection_sphere_frame_of_permanent_quotient BHS 14 139 k (L.target M)
    (eta_detection_permanent_quotient_frame_of_page_six 14 139 k hk (L.target M) hp a ha hall)

private theorem eta_detection_stem125_weight133_filtration_twelve_to_fourteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (a : BiHom 125 133 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
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

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      12 14 125 133 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,125+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 137
          (by omega) (by omega) SF.e4_stem125_af12
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 13 138
          (by omega) (by omega) SF.e5_stem125_af13
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-133) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 133 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,133)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,133)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,133)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,133)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact hgap ha

private theorem eta_detection_u_choice_eta_lambda_three_filtration_fourteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toAdamsComparisonData L u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (lambdaMultiply 3 (sphereProduct η u)) := by
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
  have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M)=0 := by
    have h := I.products ⟨1,2,10,134⟩ (by simp [Raw.products]) dataH1 U
    dsimp only at h
    rw [I.distinguishedClasses.h1,(distinguished_expression_comparisons I).2.1] at h
    have hraw : mulAt dataH1 U=0 := by
      apply Subtype.ext
      change h1*((h0*h0)*(atom .x_124_8).val)=0
      rw [←mul_assoc,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,zero_mul]
    exact h.symm.trans (by rw [hraw,map_zero])
  have hfirst := eta_detection_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) u hu.1
  have hdu := D.comparisonCompatible.homotopy_lambda 10 134 3 u
  rw [hfirst] at hdu
  have hd := D.multiplicationCompatible 1 2 10 134 0 3
    (Sphere.Internal.hi H M 1) (L.U M) η (lambdaMultiply 3 u) hηd hdu
  change Detects D.sphereConvergence (11,136,133)
    (D.sphereE2 11 136 3 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M))) (sphereProduct η (lambdaMultiply 3 u)) at hd
  rw [hp,map_zero,eta_detection_eta_lambda3_right D η u] at hd
  exact eta_detection_stem125_weight133_filtration_twelve_to_fourteen BHS I SF _
    (detects_zero_filtration D.sphereConvergence (11,136,133) hd)

private theorem eta_detection_stem125_filtration_twelve_to_fourteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
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

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      12 14 125 130 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,125+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 137
          (by omega) (by omega) SF.e4_stem125_af12
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 13 138
          (by omega) (by omega) SF.e5_stem125_af13
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-130) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact hgap ha

private theorem eta_detection_square_detection_eta_filtration_fourteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (sphereProduct η (sphereProduct θ θ)) := by
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
  have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M)=0 := by
    have h := I.products ⟨1,2,10,134⟩ (by simp [Raw.products]) dataH1 U
    dsimp only at h
    rw [I.distinguishedClasses.h1,(distinguished_expression_comparisons I).2.1] at h
    have hraw : mulAt dataH1 U=0 := by
      apply Subtype.ext
      change h1*((h0*h0)*(atom .x_124_8).val)=0
      rw [←mul_assoc,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,zero_mul]
    exact h.symm.trans (by rw [hraw,map_zero])
  have hd := D.multiplicationCompatible 1 2 10 134 0 6
    (Sphere.Internal.hi H M 1) (L.U M) η (sphereProduct θ θ) hηd hc4.1
  change Detects D.sphereConvergence (11,136,130)
    (D.sphereE2 11 136 6 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M))) (sphereProduct η (sphereProduct θ θ)) at hd
  rw [hp,map_zero] at hd
  exact eta_detection_stem125_filtration_twelve_to_fourteen BHS I SF _
    (detects_zero_filtration D.sphereConvergence (11,136,130) hd)

private theorem eta_detection_criterion (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (BHS : SyntheticComparisonTheorems D) (SF : Derived.SphereFacts I.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I.interpretation.sphere 13 137 correction))
    (hframe6 : (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) :
    (∀ a : BiHom 125 130 (S_0_0 : Syn),VanishesModLambda 9 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a) ∧
    (∀ a : BiHom 125 130 (S_0_0 : Syn),VanishesModLambda 10 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) ∧
    (∃u,UChoice M D.toAdamsComparisonData L u) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toAdamsComparisonData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (sphereProduct eta (sphereProduct theta theta))) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toAdamsComparisonData eta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toAdamsComparisonData L u →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (lambdaMultiply 3 (sphereProduct eta u))) ∧
    (∀ e : ((D.family.sphere).sequence.ssData (14,139,133)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (14,139,133)
        (D.sphereE2 14 139 6 (L.target M)) e) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toAdamsComparisonData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toAdamsComparisonData L u →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
        ((show BiHom 125 130 (S_0_0:Syn) from sphereProduct eta (sphereProduct theta theta))-
          (show BiHom 125 130 (S_0_0:Syn) from lambdaMultiply 3 (lambdaMultiply 3 (sphereProduct eta u))))) ∧
    (∀ a : BiHom 125 133 (S_0_0:Syn),FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (lambdaMultiply 3 a)) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toAdamsComparisonData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toAdamsComparisonData L u →
      EtaExtensionDetectionAt M D.toAdamsComparisonData L eta u →
      Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M))
        (sphereProduct eta (sphereProduct theta theta))) ∧
    (SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) →
      ∀ a : BiHom 125 130 (S_0_0:Syn),
      Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M)) a →
      ¬FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) := by
  classical
  /- BHS label agreement and the actual nu-unit map transport common infinity
  representatives to the synthetic sphere, including the zero case. -/
  /- Actual convergence gives either nonzero leading detection or membership
  in the next actual tower filtration. -/
  /- The two complete frames and the intervening finite-page gap yield the
  three branches, retaining an actual lambda preimage in the last branch. -/
  have hp := SF.t_permanent_cycle
  rw [(distinguished_expression_comparisons I).2.2] at hp
  exact ⟨eta_detection_lambda_9_iff_filtration_14 BHS,eta_detection_lambda_10_iff_filtration_15 BHS,
    eta_detection_u_choice_exists I BHS SF,eta_detection_square_detection_eta_filtration_fourteen BHS I SF,
    eta_detection_u_choice_eta_lambda_three_filtration_fourteen BHS I SF,eta_detection_target_infinity_frame BHS SF hframe6 6 (by decide),
    eta_detection_theta_u_eta_filtration_error I BHS SF h13,
    eta_detection_lambda_three_preserves_filtration_fifteen BHS,
    eta_detection_square_detection_eta_detection_eta_target_detected I BHS SF h13,
    fun hs a ha=>eta_detection_target_detected_not_filtration_fifteen BHS.eInfty (L.target M) hp hs a ha⟩
end
end KIP126.Main.SectionSeven.DifferentialCriterion
