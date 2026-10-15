module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.SectionSeven.SphereClasses
public import KIP126.Main.Computation.SphereAndCofiber
public import KIP126.Main.ExtensionLaws.GeneralizedMahowald.Proofs

-- The CSV coordinate calculations use the defining string and list equations.
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

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
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

section NuThreeActualProof

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Classical.Adams.PageRepresentatives KIP126.Classical.Adams.Suspension
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Synthetic.PageExtension
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra KIP126.Literature.AdamsSynthetic
open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126 KIP126.LinE2 KIP126.Algebra
open scoped ZeroObject
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD homogeneousPart
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : TmfDetectionClasses H}


set_option maxHeartbeats 16000000 in
private theorem nu_three_actual_relation_and_unique
    (BHS : EInftyComparison D') (A : MayContext Syn) (I' : AdamsComputationTheorems D' L' G)
    (ap : NuCofiberNormalization D')
    (gmw : KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D' D'.hopfAndDetector.nuCofiberTriangle 0)
    (hd : Derived.CnuDifferential I'.interpretation) (SF : Derived.SphereFacts I'.interpretation) :
    (∀u v:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3),u≠0→v≠0→u=v) ∧
    ∃ κ : XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0 : Syn) 3),
      XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3≫κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0 : Syn) 3) ∧
    ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3))
      (y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3)),
      x≠0 ∧ FiniteDetected D' 3 (by decide) 8 130 0 (I'.interpretation.sphere 8 130 X) x ∧
      FiniteDetected D' 3 (by decide) 11 136 2 (I'.interpretation.sphere 11 136 Y) y ∧
      ((susp_invariance 122 130 3 4 (XModLambdaN (S_0_0 : Syn) 3)) x)≫κ.inv≫
        XModLambdaN.map (normalizedNu D' ap.nu_exponent) 3=y := by
  classical
  have differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
      (hr0 : E.r₀ ≤ r) (hrt : r < t)
      (h : HasDifferential E r p q x y) : RepresentsOnPage E t q y 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.differential_target_later_zero hr0 hrt h
  have boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)} {X : C}
      {r : ℤ} {p : ℤ×ℤ} {x : Ambient H X p}
      (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x 0) :
      x ∈ boundaries H X (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit X
    let P := E.ssData p
    obtain ⟨hr,z,hz,hzero⟩ := hx
    change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
    change P.pageπ ↑(r-2).toNat z=0 at hzero
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
    have hrindex : r-1-1=r-2 := by omega
    change ∃ y, boundaryMap H X ↑(r-1-1).toNat p y=x
    rw [hrindex]
    refine ⟨y,?_⟩
    have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
        cycleMap H X ↑(r-2).toNat p = boundaryMap H X ↑(r-2).toNat p := by
      dsimp only [boundaryMap,cycleMap,P,E]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    rw [←hf,CategoryTheory.comp_apply,hy]
    exact hz
  have differential_target_permanent {H : Mod2EilenbergMacLane (C:=C)} {X : C} {r : ℤ} {p q : ℤ×ℤ}
      {x : Ambient H X p} {y : Ambient H X q}
      (h : DifferentialAt H X r p q x y) : IsPermanent H X q y := by
    have hr : (adamsTowerInternalSpectralSequence H.unit X).r₀≤r := h.1
    have hzero := differential_target_later_zero (E:=adamsTowerInternalSpectralSequence H.unit X)
      (r:=r) (t:=r+1) (p:=p) (q:=q) hr (by omega) h.2
    have hb := boundary_of_zero_representative (H:=H) (X:=X) (r:=r+1) (p:=q) hzero
    exact boundaries_le_permanentCycles H X q (r+1-1) hb
  have raw_cycles_iff {H : Mod2EilenbergMacLane (C:=C)} (Y:C) (r:ℕ) (hr:1≤r) (s t:ℤ)
   (a:adamsE1 H.unit Y s t) :
   a∈adamsCycles H.unit Y r hr s t ↔
   ∃c:HomotopyGroup (t-s) ((adamsTowerAt H.unit Y (s+r))⟦(1:ℤ)⟧),
   c≫(adamsTowerMapAt H.unit Y (s+1) (s+r) (by omega))⟦(1:ℤ)⟧' =
   a≫HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit Y s (s+1) (by omega)) := by
   constructor
   · rintro ⟨b,hb⟩
     obtain ⟨c,hc⟩ := (homotopyDesuspend_bijective (adamsTowerAt H.unit Y (s+r)) (t-s)).2 b
     refine ⟨c,?_⟩
     apply (homotopyDesuspend_bijective (adamsTowerAt H.unit Y (s+1)) (t-s)).1
     rw [homotopyDesuspend_postcompose,hc]
     change b≫adamsTowerMapAt H.unit Y (s+1) (s+r) _ =
       connectingHomomorphism (HoCofiberSequence.ofMorphism
         (adamsTowerMapAt H.unit Y s (s+1) (by omega))) (t-s) a at hb
     rw [connectingHomomorphism_eq_desuspend] at hb
     exact hb
   · rintro ⟨c,hc⟩
     refine ⟨homotopyDesuspend (adamsTowerAt H.unit Y (s+r)) (t-s) c,?_⟩
     change _≫adamsTowerMapAt H.unit Y (s+1) (s+r) _ =
       connectingHomomorphism (HoCofiberSequence.ofMorphism
         (adamsTowerMapAt H.unit Y s (s+1) (by omega))) (t-s) a
     rw [connectingHomomorphism_eq_desuspend,←homotopyDesuspend_postcompose,hc]
     rfl
  have desuspend_mem_raw_cycles {H : Mod2EilenbergMacLane (C:=C)} {X : C} (S:TowerComparison H X)
   (r:ℕ) (hr:1≤r) (s t:ℤ) (a:adamsE1 H.unit (X⟦(1:ℤ)⟧) s t)
   (ha:a∈adamsCycles H.unit (X⟦(1:ℤ)⟧) r hr s t) :
   S.desuspendFirstPage s t a∈adamsCycles H.unit X r hr s (t-1) := by
   obtain ⟨c,hc⟩ := (raw_cycles_iff _ r hr s t a).mp ha
   let R := shiftFunctorComm C (1:ℤ) (1:ℤ)
   let e := c≫(S.tower (s+r)).hom⟦(1:ℤ)⟧'≫R.inv.app (adamsTowerAt H.unit X (s+r))
   have he : e≫(adamsTowerMapAt H.unit X (s+1) (s+r) (by omega))⟦(1:ℤ)⟧'⟦(1:ℤ)⟧' =
     -(a≫(S.layer s).hom≫(HasFunctorialCofiber.cofibδ
       (adamsTowerMapAt H.unit X s (s+1) (by omega)))⟦(1:ℤ)⟧') := by
     dsimp only [e]
     simp only [Category.assoc]
     erw [← R.inv.naturality]
     simp only [Functor.comp_map]
     rw [← CategoryTheory.Functor.map_comp_assoc, S.tower_comm, CategoryTheory.Functor.map_comp]
     simp only [←Category.assoc]
     erw [hc]
     simp only [Category.assoc]
     have hs := S.layer_connecting s
     have hs' := congrArg (fun f => f≫R.inv.app (adamsTowerAt H.unit X (s+1))) hs
     simp only [R, Category.assoc, Iso.hom_inv_id_app, Preadditive.neg_comp] at hs'
     erw [Category.comp_id] at hs'
     erw [hs']
     simp only [Preadditive.comp_neg,neg_neg]
     rfl
   apply (raw_cycles_iff X r hr s (t-1) _).mpr
   let j := eqToHom (congrArg (Sphere (C:=C)) (show (t-1)-s=(t-s)-1 by omega))
   refine ⟨-(j≫homotopyDesuspend ((adamsTowerAt H.unit X (s+r))⟦(1:ℤ)⟧) (t-s) e),?_⟩
   rw [Preadditive.neg_comp, Category.assoc, ←homotopyDesuspend_postcompose, he, map_neg]
   simp only [Preadditive.comp_neg,neg_neg]
   rw [←Category.assoc a]
   erw [homotopyDesuspend_postcompose]
   exact (Category.assoc _ _ _).symm
  have class_cycle_iff {H : Mod2EilenbergMacLane (C:=C)} (Y:C) (s t:ℤ) (k:ℕ)
   (a:adamsCycles H.unit Y 2 (by decide) s t) :
   classOfSecondCycle H Y s t a ∈ PageRepresentatives.cycles H Y ((k:ℤ)+1) (s,t) ↔
   a.val ∈ adamsCycles H.unit Y (k+2) (by omega) s t := by
     with_unfolding_all
     let W := adamsFiniteCycleSubmodule H.unit Y s t k
     let e := submoduleUnderlyingIso («M»:=ModuleCat.of ℤ (adamsCycleAmbient H.unit Y s t)) W
     have hW : W ≤ adamsFiniteCycleSubmodule H.unit Y s t 0 :=
       adamsFiniteCycleSubmodule_antitone H.unit Y s t (Nat.zero_le k)
     have hp (w:W) :
         PageRepresentatives.cycleMap H Y (k:WithTop ℕ) (s,t) (e.inv w) =
         classOfSecondCycle H Y s t w.val := by
       apply (ModuleCat.mono_iff_injective (adamsTowerSSDataPageIso H.unit Y s t 0).hom).mp inferInstance
       have h := congrArg (fun f => f w)
         (adamsTowerSSDataPageIso_submodule_π H.unit Y s t 0 W hW)
       change _ = (adamsCycleBoundaries H.unit Y 2 (by omega) s t).mkQ w.val at h
       change _ = (adamsTowerSSDataPageIso H.unit Y s t 0).hom
         ((adamsTowerSSDataPageIso H.unit Y s t 0).inv _)
       rw [Iso.inv_hom_id_apply]
       exact h
     change (∃ z, PageRepresentatives.cycleMap H Y (↑(((k:ℤ)+1)-1).toNat) (s,t) z = _) ↔ _
     have hi : ((k:ℤ)+1-1).toNat=k := by omega
     rw [hi]
     constructor
     · rintro ⟨z,hz⟩
       let w:W := e.hom z
       have hw : classOfSecondCycle H Y s t w.val=classOfSecondCycle H Y s t a := by
         rw [←hp w]
         change PageRepresentatives.cycleMap H Y (k:WithTop ℕ) (s,t) (e.inv (e.hom z)) = _
         exact (congrArg (fun zz => PageRepresentatives.cycleMap H Y (k:WithTop ℕ) (s,t) zz)
           (Iso.hom_inv_id_apply e z)).trans hz
       have hq := congrArg (fun x => (adamsTowerSSDataPageIso H.unit Y s t 0).hom x) hw
       simp only [classOfSecondCycle, Iso.inv_hom_id_apply] at hq
       have hd : a.val-w.val.val∈adamsBoundaries H.unit Y 2 (by decide) s t :=
         (Submodule.Quotient.eq (adamsCycleBoundaries H.unit Y 2 (by decide) s t)).mp hq.symm
       have hc : a.val-w.val.val∈adamsCycles H.unit Y (k+2) (by omega) s t := by
         obtain ⟨b,_,hb⟩ := hd
         rw [←hb]
         exact adamsJ_mem_cycles H.unit Y (k+2) (by omega) s t b
       simpa only [Submodule.coe_subtype, sub_add_cancel] using (adamsCycles H.unit Y (k+2) (by omega) s t).add_mem hc w.property
     · intro ha
       exact ⟨e.inv ⟨a,ha⟩,hp ⟨a,ha⟩⟩
  have desuspendsClass_isCycle {H : Mod2EilenbergMacLane (C:=C)} {X : C} (S:TowerComparison H X)
   (level s t:ℤ) (sx:PageRepresentatives.Ambient H (X⟦(1:ℤ)⟧) (s,t))
   (x:PageRepresentatives.Ambient H X (s,t-1))
   (h:S.DesuspendsClass s t sx x)
   (hc:PageRepresentatives.IsCycle H (X⟦(1:ℤ)⟧) level (s,t) sx) :
   PageRepresentatives.IsCycle H X level (s,t-1) x := by
   obtain ⟨a,b,ha,hb,hab⟩ := h
   refine ⟨hc.1,?_⟩
   let k := (level-1).toNat
   have hlevel := hc.1
   have hk : level=(k:ℤ)+1 := by dsimp [k]; omega
   rw [hk] at hc ⊢
   rw [←ha] at hc
   rw [←hb]
   apply (class_cycle_iff X s (t-1) k b).mpr
   rw [←hab]
   exact desuspend_mem_raw_cycles S (k+2) (by omega) s t a.val
     ((class_cycle_iff (X⟦(1:ℤ)⟧) s t k a).mp hc.2)
  have family_map_data {D' : AdamsComparison H M' Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp {D' : AdamsComparison H M' Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i ≫ familyPageMap D'.family g r i = familyPageMap D'.family (f ≫ g) r i := by
    rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map {D' : AdamsComparison H M' Syn}
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
  have sphere_quotient_label_to_nu {D' : AdamsComparison H M' Syn} (q k : ℕ) (s t : ℤ)
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
          ConcreteCategory.congr_hom (family_page_comp (D':=D') (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
        _ = targetNuLabel D' .sphere s t k x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          dsimp only [targetNuLabel]
          congr 1
    have hlabel : familyPageMap D'.family f 2 (s,t,t-k) (D'.quotientLabel q s t k x)=
        finiteTargetLabel D' .sphere q s t k x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D'.nu.unitIso.inv q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp (D':=D') (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)) :=
          (ConcreteCategory.congr_hom (family_page_comp (D':=D') D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)).symm
        _ = finiteTargetLabel D' .sphere q s t k x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
    exact hlabel
  have detection_exists_of_infinity {D' : AdamsComparison H M' Syn}
      {X : Syn} (c : TowerConvergence (nuCoefficientUnit H.unit D'.nu) D'.family X)
      (i : Tridegree) (x : (D'.family.obj X).E₂ i)
      (e : ((D'.family.obj X).sequence.ssData i).eInfty)
      (hx : HasInfinityRepresentative (D'.family.obj X) 2 i x e) (hne : e≠0) :
      ∃ a : BiHom (i.2.1-i.1) i.2.2 X, DetectsNonzero c i x a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) X
    haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
      inferInstance ((c.identification i).hom e)
    exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,⟨e,hx,a,rfl,ha.symm⟩,e,hx,hne⟩
  have zero_shift_quotient_label_8 {D' : AdamsComparison H M' Syn}
      (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      familyPageMap D'.family
        (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) ⟶ D'.nu.functor.obj (X.obj D'.hopfAndDetector) from SyntheticCategory.biShift_zero.hom.app _) q)
        2 (8,134,134-(0:ℕ))
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 8 134 0 x) =
      (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 8 134 0 x) := by
    let A := D'.nu.functor.obj (X.obj D'.hopfAndDetector)
    let a : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ (8,134,134-(0:ℕ)) := by
      simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using D'.nuE2 X 0 8 134 0 x
    change familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (8,134,134-(0:ℕ))
      (familyPageMap D'.family (XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ)) a) =
        familyPageMap D'.family (XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ))
          (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app A) 2 (8,134,134-(0:ℕ)) a)
    calc
      _ = familyPageMap D'.family
          (XModLambdaN.incl _ q≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (8,134,134-(0:ℕ)) a :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134-(0:ℕ))) a
      _ = familyPageMap D'.family
          (SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ)) a := by
        rw [XModLambdaN.incl_naturality]
      _ = _ := (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134-(0:ℕ))) a).symm
  have zero_shift_quotient_label_inverse_8 {D' : AdamsComparison H M' Syn}
      (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      familyPageMap D'.family
        (XModLambdaN.map (show D'.nu.functor.obj (X.obj D'.hopfAndDetector) ⟶ (SyntheticCategory.biShift (0,0)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) from SyntheticCategory.biShift_zero.inv.app _) q)
        2 (8,134,134-(0:ℕ))
        (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 8 134 0 x) =
      (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 8 134 0 x) := by
    let A := D'.nu.functor.obj (X.obj D'.hopfAndDetector)
    let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
    let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
    have hfg : f≫g=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.hom_inv_id_app,D'.quotientFunctoriality.map_id]
    rw [←zero_shift_quotient_label_8 (D':=D') X q x]
    change familyPageMap D'.family g 2 (8,134,134-(0:ℕ))
      (familyPageMap D'.family f 2 (8,134,134-(0:ℕ)) _) = _
    rw [←ConcreteCategory.comp_apply]
    rw [family_page_comp (D':=D') f g 2 (8,134,134-(0:ℕ)),hfg,family_map_data,D'.family.functor.map_id]
    exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
      (D'.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q)).ssData (8,134,134-(0:ℕ))
      ↑(2-2:ℤ).toNat) _
  have zero_shift_finite_infinity_exists_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (q : ℕ) (hq : 0<q)
      (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (8,134)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D'.nu D'.hopfAndDetector)).sequence.ssData (8,134,134-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (8,134,134-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 8 134 0 x) e := by
    let P := BHS.presentation.finiteWindow (X.obj D'.hopfAndDetector) q hq (8,134) (134-(0:ℕ)) (by constructor <;> omega)
    let c : PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-134+(134-(0:ℕ))) (8,134) :=
      ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
    let en := P.symm (NestedQuotient.projection _ _ c)
    have hen : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q)
        2 (8,134,134-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 8 134 0 x) en := by
      exact (BHS.labels.1 X q hq (8,134) 0 hq c en).mpr (P.apply_symm_apply _)
    let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q
    refine ⟨(D'.family.functor.map g).eInftyMap (8,134,134-(0:ℕ)) en,?_⟩
    have he := family_infinity_representative_map (D':=D') g (8,134,134-(0:ℕ)) _ en hen
    dsimp only [g,id] at he
    have hl := zero_shift_quotient_label_inverse_8 (D':=D') X q x
    convert he using 1
    · rfl
    · exact hl.symm
  have zero_shift_quotient_label_11 {D' : AdamsComparison H M' Syn}
      (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      familyPageMap D'.family
        (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) ⟶ D'.nu.functor.obj (X.obj D'.hopfAndDetector) from SyntheticCategory.biShift_zero.hom.app _) q)
        2 (11,136,136-(0:ℕ))
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 11 136 0 x) =
      (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 11 136 0 x) := by
    let A := D'.nu.functor.obj (X.obj D'.hopfAndDetector)
    let a : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ (11,136,136-(0:ℕ)) := by
      simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using D'.nuE2 X 0 11 136 0 x
    change familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (11,136,136-(0:ℕ))
      (familyPageMap D'.family (XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ)) a) =
        familyPageMap D'.family (XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ))
          (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app A) 2 (11,136,136-(0:ℕ)) a)
    calc
      _ = familyPageMap D'.family
          (XModLambdaN.incl _ q≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (11,136,136-(0:ℕ)) a :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136-(0:ℕ))) a
      _ = familyPageMap D'.family
          (SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ)) a := by
        rw [XModLambdaN.incl_naturality]
      _ = _ := (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136-(0:ℕ))) a).symm
  have zero_shift_quotient_label_inverse_11 {D' : AdamsComparison H M' Syn}
      (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      familyPageMap D'.family
        (XModLambdaN.map (show D'.nu.functor.obj (X.obj D'.hopfAndDetector) ⟶ (SyntheticCategory.biShift (0,0)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) from SyntheticCategory.biShift_zero.inv.app _) q)
        2 (11,136,136-(0:ℕ))
        (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 11 136 0 x) =
      (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 11 136 0 x) := by
    let A := D'.nu.functor.obj (X.obj D'.hopfAndDetector)
    let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
    let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
    have hfg : f≫g=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.hom_inv_id_app,D'.quotientFunctoriality.map_id]
    rw [←zero_shift_quotient_label_11 (D':=D') X q x]
    change familyPageMap D'.family g 2 (11,136,136-(0:ℕ))
      (familyPageMap D'.family f 2 (11,136,136-(0:ℕ)) _) = _
    rw [←ConcreteCategory.comp_apply]
    rw [family_page_comp (D':=D') f g 2 (11,136,136-(0:ℕ)),hfg,family_map_data,D'.family.functor.map_id]
    exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
      (D'.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q)).ssData (11,136,136-(0:ℕ))
      ↑(2-2:ℤ).toNat) _
  have zero_shift_finite_infinity_exists_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (q : ℕ) (hq : 0<q)
      (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (11,136)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D'.nu D'.hopfAndDetector)).sequence.ssData (11,136,136-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (11,136,136-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D' X q 0 11 136 0 x) e := by
    let P := BHS.presentation.finiteWindow (X.obj D'.hopfAndDetector) q hq (11,136) (136-(0:ℕ)) (by constructor <;> omega)
    let c : PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-136+(136-(0:ℕ))) (11,136) :=
      ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
    let en := P.symm (NestedQuotient.projection _ _ c)
    have hen : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q)
        2 (11,136,136-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D' X q 11 136 0 x) en := by
      exact (BHS.labels.1 X q hq (11,136) 0 hq c en).mpr (P.apply_symm_apply _)
    let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q
    refine ⟨(D'.family.functor.map g).eInftyMap (11,136,136-(0:ℕ)) en,?_⟩
    have he := family_infinity_representative_map (D':=D') g (11,136,136-(0:ℕ)) _ en hen
    dsimp only [g,id] at he
    have hl := zero_shift_quotient_label_inverse_11 (D':=D') X q x
    convert he using 1
    · rfl
    · exact hl.symm
  have elementMap_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
      elementMap x ≫ f = elementMap (f x) := by
    ext a
    simp [elementMap]
  have strict_fiber_elements (FC : FilteredComplex (ModuleCat.{v} ℤ))
      (n s k : ℤ) (x : FC.assocGraded s k) (y : FC.assocGraded (s+n) (k-1)) :
      Nonempty (FilteredComplex.Solutions.Fiber FC n s k (elementMap x) (elementMap y)) ↔
        ∃ (a : (Subobject.underlying.obj (FC.fil s k) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj (FC.fil (s+n) (k-1)) : ModuleCat.{v} ℤ)),
          FC.filToAssocGraded s k a=x ∧ FC.filToAssocGraded (s+n) (k-1) b=y ∧
          FC.d k ((FC.fil s k).arrow a)=(FC.fil (s+n) (k-1)).arrow b := by
    constructor
    · rintro ⟨W⟩
      obtain ⟨hx,hy,he⟩ := (FilteredComplex.Solutions.mem_fiber_iff W.val).mp W.property
      refine ⟨W.val.1.hom (ULift.up 1),W.val.2.hom (ULift.up 1),?_,?_,?_⟩
      · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hx
        simpa [FilteredComplex.IsLift,elementMap] using hh
      · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hy
        simpa [FilteredComplex.IsLift,elementMap] using hh
      · exact congrArg (fun f => f.hom (ULift.up (1:ℤ))) he
    · rintro ⟨a,b,ha,hb,he⟩
      refine ⟨⟨(elementMap a,elementMap b),(FilteredComplex.Solutions.mem_fiber_iff _).mpr ⟨?_,?_,?_⟩⟩⟩
      · change elementMap a ≫ FC.filToAssocGraded s k=elementMap x
        rw [elementMap_comp,ha]
      · change elementMap b ≫ FC.filToAssocGraded (s+n) (k-1)=elementMap y
        rw [elementMap_comp,hb]
      · rw [←Category.assoc,elementMap_comp,elementMap_comp,elementMap_comp,he]
  have actual_extension_strict_elements {D' : AdamsComparison H M' Syn}
      {A B : Syn} (g : A ⟶ B)
      (cx : TowerConvergence (nuCoefficientUnit H.unit D'.nu) D'.family A)
      (cy : TowerConvergence (nuCoefficientUnit H.unit D'.nu) D'.family B)
      (p : ℤ×ℤ) (s n : ℤ)
      (x : ((D'.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (y : ((D'.family.obj B).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) :
      ExtensionEquation g cx cy p s n x y ↔
        0≤n ∧ ∃ (a : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D'.nu) A).F s p) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D'.nu) B).F (s+n) p) : ModuleCat.{v} ℤ)),
          (towerFiltration (nuCoefficientUnit H.unit D'.nu) A).toAssociatedGraded s p a =
            (extensionSourceIso (nuCoefficientUnit H.unit D'.nu) g cx p s).hom x ∧
          (towerFiltration (nuCoefficientUnit H.unit D'.nu) B).toAssociatedGraded (s+n) p b =
            (extensionTargetIso (nuCoefficientUnit H.unit D'.nu) g cy p (s+n)).hom y ∧
          ((towerFiltration (nuCoefficientUnit H.unit D'.nu) A).F s p).arrow a ≫ g =
            ((towerFiltration (nuCoefficientUnit H.unit D'.nu) B).F (s+n) p).arrow b := by
    unfold ExtensionEquation
    rw [strict_fiber_elements]
    simp only [extensionComplex,underlyingComplex_filToAssocGraded_one,underlyingComplex_d_one]
    rfl
  have actual_extension_zero_comparison {D' : AdamsComparison H M' Syn}
      (A B : SyntheticObject) (g : A.obj D'.nu D'.hopfAndDetector ⟶ B.obj D'.nu D'.hopfAndDetector)
      (p : ℤ×ℤ) (s : ℤ) :
      (extensionSourceIso (nuCoefficientUnit H.unit D'.nu) g (D'.convergence A) p s).hom ≫
        (extensionComplex (nuCoefficientUnit H.unit D'.nu) g p).assocGradedDiff s 1 =
      (D'.family.functor.map g).eInftyMap (s,p.1+s,p.2) ≫
        (extensionTargetIso (nuCoefficientUnit H.unit D'.nu) g (D'.convergence B) p s).hom := by
    obtain ⟨c,hca,hce⟩ := D'.comparisonCompatible.convergence_natural A B g
    have hc := c.iso_compat (s,p.1+s,p.2)
    simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,
      SyntheticAdamsConvergence.toConvergence] at hc
    rw [hce] at hc
    have hd : (extensionComplex (nuCoefficientUnit H.unit D'.nu) g p).assocGradedDiff s 1 =
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p := by
      haveI : Epi ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
        (A.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
      apply (cancel_epi ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
        (A.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s p)).mp
      change _ ≫ (underlyingComplex (syntheticHomotopyMap g) (homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D'.nu) g) p).assocGradedDiff s 1 = _
      rw [underlyingComplex_assocGradedDiff_compat_one]
      have hq : (towerFiltration (nuCoefficientUnit H.unit D'.nu) (A.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s p ≫
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p =
          (c.filtration_compat s p).choose ≫ (towerFiltration (nuCoefficientUnit H.unit D'.nu) (B.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s p := by
        exact cokernel.π_desc _ _ _
      rw [hq]
      congr 1
      apply (cancel_mono ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
        (B.obj D'.nu D'.hopfAndDetector)).F s p).arrow).mp
      rw [(homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D'.nu) g s p).choose_spec]
      let k := (c.filtration_compat s p).choose
      have hk : k ≫ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (B.obj D'.nu D'.hopfAndDetector)).F s p).arrow =
          ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (A.obj D'.nu D'.hopfAndDetector)).F s p).arrow ≫ c.aMap p :=
        (c.filtration_compat s p).choose_spec
      change k ≫
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (B.obj D'.nu D'.hopfAndDetector)).F s p).arrow =
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (A.obj D'.nu D'.hopfAndDetector)).F s p).arrow ≫ c.aMap p at hk
      rw [hca] at hk
      exact hk.symm
    rw [hd]
    have transport {ι : Type} (P Q : ι → ModuleCat.{v} ℤ) (F : ∀i, P i ⟶ Q i)
        {i j : ι} (h : i=j) {U V : ModuleCat.{v} ℤ} (a : U ⟶ P i) (b : V ⟶ Q i)
        (g : U ⟶ V) (he : g≫b=a≫F i) :
        (a≫eqToHom (congrArg P h))≫F j=g≫(b≫eqToHom (congrArg Q h)) := by
      subst j
      simpa only [eqToHom_refl,Category.comp_id] using he.symm
    exact transport (ι:=ℤ×ℤ) (i:=(p.1+s-s,p.2)) (j:=p)
      (fun m => (towerFiltration (nuCoefficientUnit H.unit D'.nu) (A.obj D'.nu D'.hopfAndDetector)).associatedGraded s m)
      (fun m => (towerFiltration (nuCoefficientUnit H.unit D'.nu) (B.obj D'.nu D'.hopfAndDetector)).associatedGraded s m)
      (fun m => Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m)
      (show (p.1+s-s,p.2)=p by ext <;> simp)
      ((D'.convergence A).identification (s,p.1+s,p.2)).hom
      ((D'.convergence B).identification (s,p.1+s,p.2)).hom
      ((D'.family.functor.map g).eInftyMap (s,p.1+s,p.2)) hc
  have actual_extension_zero_8 {D' : AdamsComparison H M' Syn}
      (A B : SyntheticObject) (g : A.obj D'.nu D'.hopfAndDetector ⟶ B.obj D'.nu D'.hopfAndDetector)
      (w : ℤ) (x : ((D'.family.obj (A.obj D'.nu D'.hopfAndDetector)).sequence.ssData (8,134,w)).eInfty) :
      ExtensionEquation g (D'.convergence A) (D'.convergence B) (126,w) 8 0 x
        ((D'.family.functor.map g).eInftyMap (8,134,w) x) := by
    refine ⟨le_refl _,?_⟩
    apply (strict_fiber_elements _ 0 8 1 _ _).mpr
    let FC := extensionComplex (nuCoefficientUnit H.unit D'.nu) g (126,w)
    let xx := (extensionSourceIso (nuCoefficientUnit H.unit D'.nu) g (D'.convergence A) (126,w) 8).hom x
    haveI : Epi (FC.filToAssocGraded 8 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (FC.filToAssocGraded 8 1)).mp inferInstance xx
    refine ⟨c,FC.filDiff 8 1 c,hc,?_,?_⟩
    · have h := ConcreteCategory.congr_hom (actual_extension_zero_comparison A B g (126,w) 8) x
      have hh := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat 8 1) c
      change FC.assocGradedDiff 8 1 (FC.filToAssocGraded 8 1 c)=FC.filToAssocGraded 8 0 (FC.filDiff 8 1 c) at hh
      rw [hc] at hh
      exact hh.symm.trans h
    · exact (ConcreteCategory.congr_hom (FC.differential_preserves 8 1).choose_spec c).symm
  have actual_extension_zero_11 {D' : AdamsComparison H M' Syn}
      (A B : SyntheticObject) (g : A.obj D'.nu D'.hopfAndDetector ⟶ B.obj D'.nu D'.hopfAndDetector)
      (w : ℤ) (x : ((D'.family.obj (A.obj D'.nu D'.hopfAndDetector)).sequence.ssData (11,136,w)).eInfty) :
      ExtensionEquation g (D'.convergence A) (D'.convergence B) (125,w) 11 0 x
        ((D'.family.functor.map g).eInftyMap (11,136,w) x) := by
    refine ⟨le_refl _,?_⟩
    apply (strict_fiber_elements _ 0 11 1 _ _).mpr
    let FC := extensionComplex (nuCoefficientUnit H.unit D'.nu) g (125,w)
    let xx := (extensionSourceIso (nuCoefficientUnit H.unit D'.nu) g (D'.convergence A) (125,w) 11).hom x
    haveI : Epi (FC.filToAssocGraded 11 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (FC.filToAssocGraded 11 1)).mp inferInstance xx
    refine ⟨c,FC.filDiff 11 1 c,hc,?_,?_⟩
    · have h := ConcreteCategory.congr_hom (actual_extension_zero_comparison A B g (125,w) 11) x
      have hh := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat 11 1) c
      change FC.assocGradedDiff 11 1 (FC.filToAssocGraded 11 1 c)=FC.filToAssocGraded 11 0 (FC.filDiff 11 1 c) at hh
      rw [hc] at hh
      exact hh.symm.trans h
    · exact (ConcreteCategory.congr_hom (FC.differential_preserves 11 1).choose_spec c).symm
  have lambda_to_positive_zero (D' : AdamsComparison H M' Syn) (A : Syn) :
      lambdaToPositivePow 0 A = SyntheticCategory.biShift_zero.inv.app A := by
    have hc := D'.shiftCoherence.right_unit (0,0) A
    have he : (SyntheticCategory.biShift_comp (0,0) (0,0)).hom.app A =
        SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A) := by
      change (biShiftAddIso (0,0) (0,0) (0,0) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id] using hc
    dsimp only [lambdaToPositivePow,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    change SyntheticCategory.biShift_zero.inv.app A ≫
      (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
        SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A)=_
    calc
      _ = SyntheticCategory.biShift_zero.inv.app A ≫
          (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
            (SyntheticCategory.biShift_comp (0,0) (0,0)).hom.app A := by
        exact congrArg (fun k => SyntheticCategory.biShift_zero.inv.app A ≫
          (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫ k) he.symm
      _ = SyntheticCategory.biShift_zero.inv.app A := by
        rw [Iso.inv_hom_id_app]
        exact Category.comp_id _
  have target_nu_natural_8 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      familyPageMap D'.family (D'.nu.functor.map f) 2 (8,134,134) (targetNuLabel D' X 8 134 0 x) =
        targetNuLabel D' Y 8 134 0 (adamsInternalE2Induced H.unit f (8,134) x) := by
    have h := D'.comparisonCompatible.nu_natural X Y f 0 8 134 0 x
    change familyPageMap D'.family (D'.nu.functor.map f) 2 (8,134,134)
      (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) (D'.nuE2 X 0 8 134 0 x)) = _
    calc
      _ = familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _≫D'.nu.functor.map f) 2 (8,134,134) (D'.nuE2 X 0 8 134 0 x) :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134)) _
      _ = familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f)≫SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) (D'.nuE2 X 0 8 134 0 x) := by
        exact congrArg (fun g => familyPageMap D'.family g 2 (8,134,134) (D'.nuE2 X 0 8 134 0 x)) (SyntheticCategory.biShift_zero.hom.naturality (D'.nu.functor.map f)).symm
      _ = familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134)
          (familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f)) 2 (8,134,134) (D'.nuE2 X 0 8 134 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134)) _).symm
      _ = _ := congrArg (fun y => familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) y) h
  have finite_target_natural_8 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134)
        (finiteTargetLabel D' X q 8 134 0 x) =
        finiteTargetLabel D' Y q 8 134 0 (adamsInternalE2Induced H.unit f (8,134) x) := by
    change familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134)
      (familyPageMap D'.family (XModLambdaN.incl _ q) 2 (8,134,134) (targetNuLabel D' X 8 134 0 x)) = _
    calc
      _ = familyPageMap D'.family (XModLambdaN.incl _ q≫XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134) (targetNuLabel D' X 8 134 0 x) :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134)) _
      _ = familyPageMap D'.family (D'.nu.functor.map f≫XModLambdaN.incl _ q) 2 (8,134,134) (targetNuLabel D' X 8 134 0 x) :=
        congrArg (fun g => familyPageMap D'.family g 2 (8,134,134) (targetNuLabel D' X 8 134 0 x)) (XModLambdaN.incl_naturality (D'.nu.functor.map f) q).symm
      _ = familyPageMap D'.family (XModLambdaN.incl _ q) 2 (8,134,134)
          (familyPageMap D'.family (D'.nu.functor.map f) 2 (8,134,134) (targetNuLabel D' X 8 134 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134)) _).symm
      _ = _ := congrArg (fun y => familyPageMap D'.family (XModLambdaN.incl _ q) 2 (8,134,134) y) (target_nu_natural_8 (D':=D') X Y f x)
  have target_nu_natural_11 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      familyPageMap D'.family (D'.nu.functor.map f) 2 (11,136,136) (targetNuLabel D' X 11 136 0 x) =
        targetNuLabel D' Y 11 136 0 (adamsInternalE2Induced H.unit f (11,136) x) := by
    have h := D'.comparisonCompatible.nu_natural X Y f 0 11 136 0 x
    change familyPageMap D'.family (D'.nu.functor.map f) 2 (11,136,136)
      (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) (D'.nuE2 X 0 11 136 0 x)) = _
    calc
      _ = familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _≫D'.nu.functor.map f) 2 (11,136,136) (D'.nuE2 X 0 11 136 0 x) :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136)) _
      _ = familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f)≫SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) (D'.nuE2 X 0 11 136 0 x) := by
        exact congrArg (fun g => familyPageMap D'.family g 2 (11,136,136) (D'.nuE2 X 0 11 136 0 x)) (SyntheticCategory.biShift_zero.hom.naturality (D'.nu.functor.map f)).symm
      _ = familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136)
          (familyPageMap D'.family ((SyntheticCategory.biShift (0,0)).map (D'.nu.functor.map f)) 2 (11,136,136) (D'.nuE2 X 0 11 136 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136)) _).symm
      _ = _ := congrArg (fun y => familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) y) h
  have finite_target_natural_11 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136)
        (finiteTargetLabel D' X q 11 136 0 x) =
        finiteTargetLabel D' Y q 11 136 0 (adamsInternalE2Induced H.unit f (11,136) x) := by
    change familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136)
      (familyPageMap D'.family (XModLambdaN.incl _ q) 2 (11,136,136) (targetNuLabel D' X 11 136 0 x)) = _
    calc
      _ = familyPageMap D'.family (XModLambdaN.incl _ q≫XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136) (targetNuLabel D' X 11 136 0 x) :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136)) _
      _ = familyPageMap D'.family (D'.nu.functor.map f≫XModLambdaN.incl _ q) 2 (11,136,136) (targetNuLabel D' X 11 136 0 x) :=
        congrArg (fun g => familyPageMap D'.family g 2 (11,136,136) (targetNuLabel D' X 11 136 0 x)) (XModLambdaN.incl_naturality (D'.nu.functor.map f) q).symm
      _ = familyPageMap D'.family (XModLambdaN.incl _ q) 2 (11,136,136)
          (familyPageMap D'.family (D'.nu.functor.map f) 2 (11,136,136) (targetNuLabel D' X 11 136 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136)) _).symm
      _ = _ := congrArg (fun y => familyPageMap D'.family (XModLambdaN.incl _ q) 2 (11,136,136) y) (target_nu_natural_11 (D':=D') X Y f x)
  have zero_exponent_source_infinity_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (n : ℕ) (hn : n=0)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (8,134)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)).sequence.ssData (8,(134-8)+8,134+n)).eInfty,
        HasInfinityRepresentative _ 2 (8,(134-8)+8,134+n)
          (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)) (i:=(8,134,134+(n:ℤ)-(0:ℕ))) (j:=(8,134,134+(n:ℤ))) (by ext <;> simp) (finiteNuLabel D' X q n 8 134 0 x)) e := by
    subst n
    exact zero_shift_finite_infinity_exists_8 (D':=D') BHS X q hq x hx
  have normalized_zero_source_infinity_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject)
      (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector) (he : normalizedExponent H f=0)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (8,134)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (extensionSourceObject D' X Y f)).obj D'.nu D'.hopfAndDetector)).sequence.ssData (8,(134-8)+8,134+normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 (8,(134-8)+8,134+normalizedExponent H f)
          (finiteSourceForExtension D' X Y f q 8 134 x) e := by
    exact zero_exponent_source_infinity_8 BHS X _ he q hq x hx
  have zero_exponent_source_infinity_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (n : ℕ) (hn : n=0)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (11,136)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)).sequence.ssData (11,(136-11)+11,136+n)).eInfty,
        HasInfinityRepresentative _ 2 (11,(136-11)+11,136+n)
          (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)) (i:=(11,136,136+(n:ℤ)-(0:ℕ))) (j:=(11,136,136+(n:ℤ))) (by ext <;> simp) (finiteNuLabel D' X q n 11 136 0 x)) e := by
    subst n
    exact zero_shift_finite_infinity_exists_11 (D':=D') BHS X q hq x hx
  have normalized_zero_source_infinity_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject)
      (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector) (he : normalizedExponent H f=0)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (11,136)) :
      ∃ e : ((D'.family.obj ((SyntheticObject.quotient q (extensionSourceObject D' X Y f)).obj D'.nu D'.hopfAndDetector)).sequence.ssData (11,(136-11)+11,136+normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 (11,(136-11)+11,136+normalizedExponent H f)
          (finiteSourceForExtension D' X Y f q 11 136 x) e := by
    exact zero_exponent_source_infinity_11 BHS X _ he q hq x hx
  have zero_exponent_map_label_8 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (n : ℕ) (hn : n=0)
      (g : (SyntheticCategory.biShift (0,n)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) ⟶ D'.nu.functor.obj (Y.obj D'.hopfAndDetector))
      (hf : lambdaToPositivePow n (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g=D'.nu.functor.map f)
      (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      HEq (familyPageMap D'.family (XModLambdaN.map g q) 2 (8,(134-8)+8,134+n)
        (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)) (i:=(8,134,134+(n:ℤ)-(0:ℕ))) (j:=(8,134,134+(n:ℤ))) (by ext <;> simp) (finiteNuLabel D' X q n 8 134 0 x)))
        (finiteTargetLabel D' Y q 8 134 0 (adamsInternalE2Induced H.unit f (8,134) x)) := by
    subst n
    have hfact : SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g=D'.nu.functor.map f :=
      (congrArg (fun u => u≫g) (lambda_to_positive_zero D' _)).symm.trans hf
    have hg : g=SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫D'.nu.functor.map f := by
      calc
        _ = SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫
          SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g := by simp
        _ = _ := congrArg (fun u => SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫u) hfact
    apply heq_of_eq
    change familyPageMap D'.family (XModLambdaN.map g q) 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x) = _
    calc
      _ = familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫D'.nu.functor.map f) q) 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x) :=
        congrArg (fun u => familyPageMap D'.family (XModLambdaN.map u q) 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x)) hg
      _ = familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q≫XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x) :=
        congrArg (fun u => familyPageMap D'.family u 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x)) (D'.quotientFunctoriality.map_comp _ _ q)
      _ = familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134)
          (familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q) 2 (8,134,134) (finiteNuLabel D' X q 0 8 134 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (8,134,134)) _).symm
      _ = familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134) (finiteTargetLabel D' X q 8 134 0 x) :=
        congrArg (fun z => familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (8,134,134) z) (zero_shift_quotient_label_8 (D':=D') X q x)
      _ = _ := finite_target_natural_8 X Y f q x
  have normalized_zero_map_label_8 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (he : normalizedExponent H f=0) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 8 134) :
      HEq (familyPageMap D'.family (finiteExtensionMap D' X Y f q) 2 (8,(134-8)+8,134+normalizedExponent H f)
        (finiteSourceForExtension D' X Y f q 8 134 x))
        (finiteTargetLabel D' Y q 8 134 0 (adamsInternalE2Induced H.unit f (8,134) x)) := by
    exact zero_exponent_map_label_8 X Y f _ he (D'.normalizedMap X Y f).map (D'.normalizedMap X Y f).factorization q x
  have zero_exponent_map_label_11 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (n : ℕ) (hn : n=0)
      (g : (SyntheticCategory.biShift (0,n)).obj (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) ⟶ D'.nu.functor.obj (Y.obj D'.hopfAndDetector))
      (hf : lambdaToPositivePow n (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g=D'.nu.functor.map f)
      (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      HEq (familyPageMap D'.family (XModLambdaN.map g q) 2 (11,(136-11)+11,136+n)
        (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj D'.nu D'.hopfAndDetector)) (i:=(11,136,136+(n:ℤ)-(0:ℕ))) (j:=(11,136,136+(n:ℤ))) (by ext <;> simp) (finiteNuLabel D' X q n 11 136 0 x)))
        (finiteTargetLabel D' Y q 11 136 0 (adamsInternalE2Induced H.unit f (11,136) x)) := by
    subst n
    have hfact : SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g=D'.nu.functor.map f :=
      (congrArg (fun u => u≫g) (lambda_to_positive_zero D' _)).symm.trans hf
    have hg : g=SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫D'.nu.functor.map f := by
      calc
        _ = SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫
          SyntheticCategory.biShift_zero.inv.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫g := by simp
        _ = _ := congrArg (fun u => SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫u) hfact
    apply heq_of_eq
    change familyPageMap D'.family (XModLambdaN.map g q) 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x) = _
    calc
      _ = familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))≫D'.nu.functor.map f) q) 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x) :=
        congrArg (fun u => familyPageMap D'.family (XModLambdaN.map u q) 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x)) hg
      _ = familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q≫XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x) :=
        congrArg (fun u => familyPageMap D'.family u 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x)) (D'.quotientFunctoriality.map_comp _ _ q)
      _ = familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136)
          (familyPageMap D'.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj (X.obj D'.hopfAndDetector))) q) 2 (11,136,136) (finiteNuLabel D' X q 0 11 136 0 x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D':=D') _ _ 2 (11,136,136)) _).symm
      _ = familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136) (finiteTargetLabel D' X q 11 136 0 x) :=
        congrArg (fun z => familyPageMap D'.family (XModLambdaN.map (D'.nu.functor.map f) q) 2 (11,136,136) z) (zero_shift_quotient_label_11 (D':=D') X q x)
      _ = _ := finite_target_natural_11 X Y f q x
  have normalized_zero_map_label_11 {D' : AdamsComparison H M' Syn}
      (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (he : normalizedExponent H f=0) (q : ℕ) (x : E2 H (X.obj D'.hopfAndDetector) 11 136) :
      HEq (familyPageMap D'.family (finiteExtensionMap D' X Y f q) 2 (11,(136-11)+11,136+normalizedExponent H f)
        (finiteSourceForExtension D' X Y f q 11 136 x))
        (finiteTargetLabel D' Y q 11 136 0 (adamsInternalE2Induced H.unit f (11,136) x)) := by
    exact zero_exponent_map_label_11 X Y f _ he (D'.normalizedMap X Y f).map (D'.normalizedMap X Y f).factorization q x
  have quotient_nu_infinity_cycles_any {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (q k : ℕ) (hk : k < q) (s t : ℤ)
      (x : E2 H (X.obj D'.hopfAndDetector) s t)
      (e : ((D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q).sequence.ssData (s,t,t-k)).eInfty)
      (hx : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q) 2 (s,t,t-k)
        (finiteTargetLabel D' X q s t k x) e) :
      x ∈ PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-k) (s,t) := by
    let P := BHS.presentation
    let Zq := PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-t+(t-k)) (s,t)
    let Z1 := PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((k+1:ℕ)-t+(t-k)) (s,t)
    let Bk := PageRepresentatives.boundaries H (X.obj D'.hopfAndDetector) (1+t-(t-k)) (s,t)
    have hq : 0 < q := by omega
    have hsurj : Function.Surjective (NestedQuotient.projection Zq Bk) := by rintro ⟨a⟩; exact ⟨a,rfl⟩
    obtain ⟨x',hx'⟩ := hsurj (P.finiteWindow (X.obj D'.hopfAndDetector) q hq (s,t) (t-k) (by constructor <;> omega) e)
    have hrep' : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q) 2 (s,t,t-k)
        (finiteTargetLabel D' X q s t k x'.val) e :=
      (BHS.labels.1 X q hq (s,t) k hk x' e).mpr hx'.symm
    let rho := (D'.quotientTower (D'.nu.functor.obj (X.obj D'.hopfAndDetector))).rho (k+1) q (by omega)
    let ek := ((D'.family.functor.map rho).eInftyMap (s,t,t-k)) e
    have restrict (y : E2 H (X.obj D'.hopfAndDetector) s t)
        (hy : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q) 2 (s,t,t-k)
          (finiteTargetLabel D' X q s t k y) e) :
        HasInfinityRepresentative (D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) (k+1)) 2 (s,t,t-k)
          (finiteTargetLabel D' X (k+1) s t k y) ek := by
      have hh := family_infinity_representative_map rho (s,t,t-k) _ _ hy
      have hlabel : familyPageMap D'.family rho 2 (s,t,t-k) (finiteTargetLabel D' X q s t k y)=
          finiteTargetLabel D' X (k+1) s t k y := by
        change familyPageMap D'.family rho 2 (s,t,t-k)
          (familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) q) 2 (s,t,t-k)
            (targetNuLabel D' X s t k y)) =
          familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj (X.obj D'.hopfAndDetector)) (k+1)) 2 (s,t,t-k)
            (targetNuLabel D' X s t k y)
        rw [←CategoryTheory.comp_apply,family_page_comp]
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
      exact hlabel ▸ hh
    have hz1 : Z1 = ⊤ := by
      dsimp only [Z1]
      have hindex : ((k+1:ℕ):ℤ)-t+(t-k)=1 := by omega
      rw [hindex,PageRepresentatives.cycles_one]
    let y : Z1 := ⟨x,by rw [hz1]; trivial⟩
    let y' : Z1 := ⟨x'.val,by rw [hz1]; trivial⟩
    have hy := (BHS.labels.1 X (k+1) (by omega) (s,t) k (by omega) y ek).mp (restrict x hx)
    have hy' := (BHS.labels.1 X (k+1) (by omega) (s,t) k (by omega) y' ek).mp (restrict x'.val hrep')
    have heq : NestedQuotient.projection Z1 Bk y=NestedQuotient.projection Z1 Bk y' := hy.symm.trans hy'
    have hd : x-x'.val ∈ Bk := by
      apply (NestedQuotient.projection_eq_zero (y-y')).mp
      rw [map_sub,heq,sub_self]
    have hz : x-x'.val ∈ Zq := PageRepresentatives.boundaries_le_cycles H (X.obj D'.hopfAndDetector) (s,t) _ _ hd
    have hh := Zq.add_mem hz x'.property
    have hindex : (q:ℤ)-t+(t-k)=(q:ℤ)-k := by omega
    simpa only [sub_add_cancel,Zq,hindex] using hh
  have nu_finite_infinity_exists_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (q : ℕ) (hq : 0<q)
      (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (8,134)) :
      ∃ e : ((D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q).sequence.ssData (8,134,134)).eInfty,
        HasInfinityRepresentative _ 2 (8,134,134) (finiteTargetLabel D' X q 8 134 0 x) e := by
    let P := BHS.presentation.finiteWindow (X.obj D'.hopfAndDetector) q hq (8,134) 134 (by constructor <;> omega)
    let c : PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-134+134) (8,134) := ⟨x,by simpa using hx⟩
    refine ⟨P.symm (NestedQuotient.projection _ _ c),?_⟩
    exact (BHS.labels.1 X q hq (8,134) 0 hq c _).mpr (P.apply_symm_apply _)
  have classical_e2_map_cycles_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (8,134)) :
      adamsInternalE2Induced H.unit f (8,134) x∈PageRepresentatives.cycles H (Y.obj D'.hopfAndDetector) q (8,134) := by
    obtain ⟨e,he⟩ := nu_finite_infinity_exists_8 BHS X q hq x hx
    have h := family_infinity_representative_map (D':=D') (XModLambdaN.map (D'.nu.functor.map f) q) (8,134,134) _ _ he
    have hl := finite_target_natural_8 (D':=D') X Y f q x
    have ht : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (Y.obj D'.hopfAndDetector) q) 2 (8,134,134)
        (finiteTargetLabel D' Y q 8 134 0 (adamsInternalE2Induced H.unit f (8,134) x))
        ((D'.family.functor.map (XModLambdaN.map (D'.nu.functor.map f) q)).eInftyMap (8,134,134) e) := hl ▸ h
    have hc := quotient_nu_infinity_cycles_any BHS Y q 0 hq 8 134 _ _ ht
    simpa only [Nat.cast_zero,sub_zero] using hc
  have nu_finite_infinity_exists_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X : ClassicalObject) (q : ℕ) (hq : 0<q)
      (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (11,136)) :
      ∃ e : ((D'.family.nuQuotient D'.nu (X.obj D'.hopfAndDetector) q).sequence.ssData (11,136,136)).eInfty,
        HasInfinityRepresentative _ 2 (11,136,136) (finiteTargetLabel D' X q 11 136 0 x) e := by
    let P := BHS.presentation.finiteWindow (X.obj D'.hopfAndDetector) q hq (11,136) 136 (by constructor <;> omega)
    let c : PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) ((q:ℤ)-136+136) (11,136) := ⟨x,by simpa using hx⟩
    refine ⟨P.symm (NestedQuotient.projection _ _ c),?_⟩
    exact (BHS.labels.1 X q hq (11,136) 0 hq c _).mpr (P.apply_symm_apply _)
  have classical_e2_map_cycles_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject) (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector)
      (q : ℕ) (hq : 0<q) (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) q (11,136)) :
      adamsInternalE2Induced H.unit f (11,136) x∈PageRepresentatives.cycles H (Y.obj D'.hopfAndDetector) q (11,136) := by
    obtain ⟨e,he⟩ := nu_finite_infinity_exists_11 BHS X q hq x hx
    have h := family_infinity_representative_map (D':=D') (XModLambdaN.map (D'.nu.functor.map f) q) (11,136,136) _ _ he
    have hl := finite_target_natural_11 (D':=D') X Y f q x
    have ht : HasInfinityRepresentative (D'.family.nuQuotient D'.nu (Y.obj D'.hopfAndDetector) q) 2 (11,136,136)
        (finiteTargetLabel D' Y q 11 136 0 (adamsInternalE2Induced H.unit f (11,136) x))
        ((D'.family.functor.map (XModLambdaN.map (D'.nu.functor.map f) q)).eInftyMap (11,136,136) e) := hl ▸ h
    have hc := quotient_nu_infinity_cycles_any BHS Y q 0 hq 11 136 _ _ ht
    simpa only [Nat.cast_zero,sub_zero] using hc
  have zero_exponent_target_label_8 {D' : AdamsComparison H M' Syn}
      (Y : ClassicalObject) (q n : ℕ) (hn : n=0) (y : E2 H (Y.obj D'.hopfAndDetector) 8 134) :
      HEq (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D'.nu D'.hopfAndDetector))
        (i:=(8+0,134+0,(134+0)-((0-(n:ℤ)).toNat:ℤ)))
        (j:=(8+0,(134-8)+(8+0),134+n))
        (by subst n; decide) (finiteTargetLabel D' Y q (8+0) (134+0) (0-(n:ℤ)).toNat y))
        (finiteTargetLabel D' Y q 8 134 0 y) := by
    subst n
    rfl
  have finite_zero_extension_8 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject)
      (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector) (he : normalizedExponent H f=0)
      (x : E2 H (X.obj D'.hopfAndDetector) 8 134)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) 2 (8,134)) :
      FiniteExtension D' X Y f 3 0 8 134 x (adamsInternalE2Induced H.unit f (8,134) x) := by
    let y : E2 H (Y.obj D'.hopfAndDetector) 8 134 := adamsInternalE2Induced H.unit f (8,134) x
    have hlower : (normalizedExponent H f:ℤ)≤0 := by omega
    obtain ⟨es,hes⟩ := normalized_zero_source_infinity_8 BHS X Y f he 2 (by decide) x hx
    let et := (D'.family.functor.map (finiteExtensionMap D' X Y f 2)).eInftyMap (8,134,134+normalizedExponent H f) es
    have hm := normalized_zero_map_label_8 (D':=D') X Y f he 2 x
    have ht : HEq (finiteTargetForExtension D' X Y f 2 0 8 134 hlower y)
        (finiteTargetLabel D' Y 2 8 134 0 y) :=
      zero_exponent_target_label_8 Y 2 _ he y
    have heq := eq_of_heq (hm.trans ht.symm)
    have hmap := family_infinity_representative_map (D':=D') (finiteExtensionMap D' X Y f 2)
      (8,134,134+normalizedExponent H f) _ es hes
    have hrep : HasInfinityRepresentative (D'.family.obj ((SyntheticObject.quotient 2 (.nu Y)).obj D'.nu D'.hopfAndDetector)) 2 (8,134,134+normalizedExponent H f) (finiteTargetForExtension D' X Y f 2 0 8 134 hlower y) et := heq ▸ hmap
    have hy : y∈PageRepresentatives.cycles H (Y.obj D'.hopfAndDetector) 2 (8,134) :=
      classical_e2_map_cycles_8 BHS X Y f 2 (by decide) x hx
    have hcindex : (3:ℤ)-1-0+(normalizedExponent H f:ℤ)=2 := by omega
    have hcycle : PageRepresentatives.IsCycle H (Y.obj D'.hopfAndDetector)
        ((3:ℤ)-1-0+(normalizedExponent H f:ℤ)) (8,134) y :=
      ⟨by omega,hcindex.symm ▸ hy⟩
    exact ⟨{
      page_ge_two:=by decide
      length_lower:=hlower
      length_upper:=by omega
      source_cycle:=⟨by decide,hx⟩
      target_cycle:=hcycle
      source:=es
      target:=et
      source_rep:=hes
      target_rep:=hrep
      equation:=actual_extension_zero_8 (.quotient 2 (extensionSourceObject D' X Y f))
        (.quotient 2 (.nu Y)) (finiteExtensionMap D' X Y f 2) (134+normalizedExponent H f) es}⟩
  have zero_exponent_target_label_11 {D' : AdamsComparison H M' Syn}
      (Y : ClassicalObject) (q n : ℕ) (hn : n=0) (y : E2 H (Y.obj D'.hopfAndDetector) 11 136) :
      HEq (regradeE2 (A:=D'.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D'.nu D'.hopfAndDetector))
        (i:=(11+0,136+0,(136+0)-((0-(n:ℤ)).toNat:ℤ)))
        (j:=(11+0,(136-11)+(11+0),136+n))
        (by subst n; decide) (finiteTargetLabel D' Y q (11+0) (136+0) (0-(n:ℤ)).toNat y))
        (finiteTargetLabel D' Y q 11 136 0 y) := by
    subst n
    rfl
  have finite_zero_extension_11 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (X Y : ClassicalObject)
      (f : X.obj D'.hopfAndDetector ⟶ Y.obj D'.hopfAndDetector) (he : normalizedExponent H f=0)
      (x : E2 H (X.obj D'.hopfAndDetector) 11 136)
      (hx : x∈PageRepresentatives.cycles H (X.obj D'.hopfAndDetector) 1 (11,136)) :
      FiniteExtension D' X Y f 2 0 11 136 x (adamsInternalE2Induced H.unit f (11,136) x) := by
    let y : E2 H (Y.obj D'.hopfAndDetector) 11 136 := adamsInternalE2Induced H.unit f (11,136) x
    have hlower : (normalizedExponent H f:ℤ)≤0 := by omega
    obtain ⟨es,hes⟩ := normalized_zero_source_infinity_11 BHS X Y f he 1 (by decide) x hx
    let et := (D'.family.functor.map (finiteExtensionMap D' X Y f 1)).eInftyMap (11,136,136+normalizedExponent H f) es
    have hm := normalized_zero_map_label_11 (D':=D') X Y f he 1 x
    have ht : HEq (finiteTargetForExtension D' X Y f 1 0 11 136 hlower y)
        (finiteTargetLabel D' Y 1 11 136 0 y) :=
      zero_exponent_target_label_11 Y 1 _ he y
    have heq := eq_of_heq (hm.trans ht.symm)
    have hmap := family_infinity_representative_map (D':=D') (finiteExtensionMap D' X Y f 1)
      (11,136,136+normalizedExponent H f) _ es hes
    have hrep : HasInfinityRepresentative (D'.family.obj ((SyntheticObject.quotient 1 (.nu Y)).obj D'.nu D'.hopfAndDetector)) 2 (11,136,136+normalizedExponent H f) (finiteTargetForExtension D' X Y f 1 0 11 136 hlower y) et := heq ▸ hmap
    have hy : y∈PageRepresentatives.cycles H (Y.obj D'.hopfAndDetector) 1 (11,136) :=
      classical_e2_map_cycles_11 BHS X Y f 1 (by decide) x hx
    have hcindex : (2:ℤ)-1-0+(normalizedExponent H f:ℤ)=1 := by omega
    have hcycle : PageRepresentatives.IsCycle H (Y.obj D'.hopfAndDetector)
        ((2:ℤ)-1-0+(normalizedExponent H f:ℤ)) (11,136) y :=
      ⟨by omega,hcindex.symm ▸ hy⟩
    exact ⟨{
      page_ge_two:=by decide
      length_lower:=hlower
      length_upper:=by omega
      source_cycle:=⟨by decide,hx⟩
      target_cycle:=hcycle
      source:=es
      target:=et
      source_rep:=hes
      target_rep:=hrep
      equation:=actual_extension_zero_11 (.quotient 1 (extensionSourceObject D' X Y f))
        (.quotient 1 (.nu Y)) (finiteExtensionMap D' X Y f 1) (136+normalizedExponent H f) es}⟩
  have zero_adams_page {J:Syn} (unit:S_0_0⟶J) [(tensorLeft J).Additive]
   (Y:Syn) (hy:IsZero Y) (s t:ℤ) :
   Subsingleton ((adamsTowerInternalSpectralSequence unit Y).Page 2 (s,t)) := by
   have hz (n:ℕ):IsZero (adamsTower unit Y n) := by
     induction n with
     | zero => exact hy
     | succ n ih =>
       have hh : IsZero (J⊗adamsTower unit Y n) := (tensorLeft J).map_isZero ih
       have hi : IsIso (adamsUnit unit (adamsTower unit Y n)) := by
         have he : adamsUnit unit (adamsTower unit Y n)=(ih.iso hh).hom := ih.eq_of_src _ _
         rw [he]
         infer_instance
       have hco := Triangle.isZero₃_of_isIso₁
         (Triangle.mk (adamsUnit unit (adamsTower unit Y n))
           (HasFunctorialCofiber.cofibι _) (HasFunctorialCofiber.cofibδ _))
         (HasFunctorialCofiber.cofib_distinguished _) hi
       exact (shiftFunctor Syn (-1:ℤ)).map_isZero hco
   have hl:IsZero (adamsLayerAt unit Y s) := by
     have hi : IsIso (adamsTowerMapAt unit Y s (s+1) (by omega)) := by
       have he : adamsTowerMapAt unit Y s (s+1) (by omega)=((hz (s+1).toNat).iso (hz s.toNat)).hom :=
         (hz (s+1).toNat).eq_of_src _ _
       rw [he]
       infer_instance
     exact Triangle.isZero₃_of_isIso₁ (adamsLayerTriangle unit Y s)
       (HasFunctorialCofiber.cofib_distinguished _) hi
   haveI : Subsingleton (adamsE1 unit Y s t) := ⟨fun a b => hl.eq_of_tgt a b⟩
   haveI : Subsingleton (adamsPage unit Y 2 (by decide) s t) := inferInstance
   exact Function.Injective.subsingleton (adamsTowerSSDataPageIso unit Y s t 0).toLinearEquiv.injective
  have family_zero_page {D' : AdamsComparison H M' Syn} (A:MayContext Syn) (s t w:ℤ) :
   Subsingleton ((D'.family.obj (0:Syn)).E₂ (s,t,w)) := by
   letI := A.leftShift
   letI := A.leftExact
   letI := D'.shiftAdditive
   let unit:=nuCoefficientUnit H.unit D'.nu
   have hzraw := zero_adams_page unit ((SyntheticCategory.biShift (0,-w)).obj (0:Syn))
     ((SyntheticCategory.biShift (0,-w)).map_isZero (isZero_zero Syn)) s t
   haveI : Subsingleton (((weightTower unit (0:Syn) w).ssData (s,t)).page 0) := hzraw
   let f:=D'.towerPresentation.forward (0:Syn) w
   let g:=D'.towerPresentation.inverse (0:Syn) w
   have hfg:f.comp g=SSDataMorphism.id (fun p:ℤ×ℤ => (D'.family.obj (0:Syn)).sequence.ssData (p.1,p.2,w)) := by
     apply SSDataMorphism.ext
     funext p
     exact D'.towerPresentation.left_inv (0:Syn) w p
   have he:f.pageMap (s,t) 0≫g.pageMap (s,t) 0=𝟙 _ := by
     rw [←SSDataMorphism.pageMap_comp,hfg,SSDataMorphism.pageMap_id]
   constructor
   intro x y
   have h:f.pageMap (s,t) 0 x=f.pageMap (s,t) 0 y := Subsingleton.elim _ _
   have hh:=congrArg (fun z => g.pageMap (s,t) 0 z) h
   simpa only [←ConcreteCategory.comp_apply,he,ConcreteCategory.id_apply] using hh
  have family_page_zero {D' : AdamsComparison H M' Syn} (A:MayContext Syn) {X Y:Syn} (s t w:ℤ)
   (x:(D'.family.obj X).E₂ (s,t,w)) : familyPageMap D'.family (0:X⟶Y) 2 (s,t,w) x=0 := by
   have hh:(0:X⟶Y)=(0:X⟶(0:Syn))≫(0:(0:Syn)⟶Y) := by simp
   rw [hh,←family_page_comp,ConcreteCategory.comp_apply]
   haveI : Subsingleton ((D'.family.obj (0:Syn)).Page 2 (s,t,w)) := family_zero_page (D':=D') A s t w
   rw [Subsingleton.elim (familyPageMap D'.family (0:X⟶(0:Syn)) 2 (s,t,w) x) 0,map_zero]
  have classical_e2_comp_zero {D' : AdamsComparison H M' Syn} (A:MayContext Syn)
   (X Y Z:ClassicalObject) (f:X.obj D'.hopfAndDetector⟶Y.obj D'.hopfAndDetector)
   (g:Y.obj D'.hopfAndDetector⟶Z.obj D'.hopfAndDetector) (h:f≫g=0) (s t:ℤ)
   (x:E2 H (X.obj D'.hopfAndDetector) s t) :
   adamsInternalE2Induced H.unit g (s,t) (adamsInternalE2Induced H.unit f (s,t) x)=0 := by
   letI:=D'.nu.additive
   letI:=D'.shiftAdditive
   apply (D'.nuE2 Z 0 s t 0).injective
   rw [map_zero,←D'.comparisonCompatible.nu_natural Y Z g 0 s t 0,
     ←D'.comparisonCompatible.nu_natural X Y f 0 s t 0]
   rw [←ConcreteCategory.comp_apply,family_page_comp,←Functor.map_comp,←Functor.map_comp,h,Functor.map_zero,Functor.map_zero]
   exact family_page_zero A s t (t+0-(0:ℕ)) _
  have cnu_full_source_top {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
   (A:MayContext Syn) (I':KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
   (xbar:Page D' .nuCofiber 8 134)
   (hx:I'.interpretation.coordinateSum .nuCofiber 8 134 [0,3,4]=some xbar) :
   adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) (8,134) xbar =
   adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) (8,134)
     (I'.interpretation.basis .nuCofiber 8 134 0) := by
   have hz : HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap≫
       HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap=0 :=
     comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished D'.hopfAndDetector.nuMap)
   have kill (a:E2 H SphereSpectrum 8 134) :
       adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) (8,134)
         (adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (8,134) a)=0 :=
     classical_e2_comp_zero A .sphere .nuCofiber (.shift 1 (.shift 3 .sphere))
       (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) hz 8 134 a
   have h3 : adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap)
       (8,134) (I'.interpretation.basis .nuCofiber 8 134 3)=0 := by
     obtain ⟨a,b,_,hb,hab⟩ := I'.cofiberInclusion ⟨8,134,[2],[3]⟩ (by simp [Raw.bottomMaps])
     have hv:Raw.coordinatesValid Raw.degrees .nuCofiber 8 134 [3]=true := rfl
     change I'.interpretation.coordinateSum .nuCofiber 8 134 [3]=some b at hb
     simp only [E2Interpretation.coordinateSum,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hb
     rw [hb,←hab]
     exact kill a
   have h4 : adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap)
       (8,134) (I'.interpretation.basis .nuCofiber 8 134 4)=0 := by
     obtain ⟨a,b,_,hb,hab⟩ := I'.cofiberInclusion ⟨8,134,[3],[4]⟩ (by simp [Raw.bottomMaps])
     have hv:Raw.coordinatesValid Raw.degrees .nuCofiber 8 134 [4]=true := rfl
     change I'.interpretation.coordinateSum .nuCofiber 8 134 [4]=some b at hb
     simp only [E2Interpretation.coordinateSum,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hb
     rw [hb,←hab]
     exact kill a
   have hv:Raw.coordinatesValid Raw.degrees .nuCofiber 8 134 [0,3,4]=true := rfl
   simp only [E2Interpretation.coordinateSum,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
   rw [←hx,map_add,map_add,h3,h4,add_zero,add_zero]
  have y_basis_label {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y=I'.interpretation.basis .sphere 11 136 3 := by
    have hc := I'.monomials (⟨.sphere,11,136,["69,1,89,1","1,1,389,1","1,1,388,1","0,2,391,1","0,3,375,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 192) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (3:Fin 5)
    have heq : KIP126.Computation.Near126.Y=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨391,by decide⟩ = projection (monomialOfString "0,2,391,1")
      have hs : "0,2,391,1" ≠ "" := by decide
      have hp : (("0,2,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0,2,391,1] := by
        have split : "0,2,391,1".splitOn ","=["0","2","391","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have cnu_mahowald_finite {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (A : MayContext Syn) (I' : AdamsComputationTheorems D' L' G)
      (ap : NuCofiberNormalization D')
      (gmw : KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D' D'.hopfAndDetector.nuCofiberTriangle 0)
      (hd : Derived.CnuDifferential I'.interpretation) :
      ∃ (x : E2 H (Sphere 3) 8 133) (y' : E2 H SphereSpectrum 11 136),
        FiniteExtension D' (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap 4 3 8 133 x y' ∧
        PageRepresentatives.Congruent H SphereSpectrum 3 (11,136) y'
          (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) := by
    obtain ⟨xb,yb,hxb,hyb,hd⟩ := hd
    have hd' : PageRepresentatives.DifferentialAt H (HasFunctorialCofiber.cofib D'.hopfAndDetector.nuMap)
        3 (8,134) (11,136) xb yb := ⟨by decide,hd.toHasDifferential⟩
    have hxbcycle := hd'.cycles.1
    have hybper := differential_target_permanent hd'
    have decode_single (o : Raw.Spectrum) (s t i : ℕ)
        (hv : Raw.coordinatesValid Raw.degrees o s t [i]=true) :
        I'.interpretation.coordinateSum o s t [i]=some (I'.interpretation.basis o s t i) := by
      simp only [E2Interpretation.coordinateSum,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    obtain ⟨x0,y0,a3,a2,a1,hx0,hy0,hdesc,_⟩ := I'.cofiberBoundary
    have hx0' := Option.some.inj (hx0.symm.trans (decode_single .nuCofiber 8 134 0 rfl))
    have htop := cnu_full_source_top A I' xb hxb
    rw [←hx0'] at htop
    let sx : E2 H ((Sphere 3)⟦(1:ℤ)⟧) 8 134 := adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) (8,134) xb
    have hdesc' : (D'.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134 sx a3 := by
      change (D'.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
        (adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) (8,134) xb) a3
      exact (congrArg (fun z : E2 H ((Sphere 3)⟦(1:ℤ)⟧) 8 134 =>
        (D'.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134 z a3) htop).mpr hdesc
    have hsx : PageRepresentatives.IsCycle H ((Sphere 3)⟦(1:ℤ)⟧) 2 (8,134) sx :=
      ⟨by decide,classical_e2_map_cycles_8 BHS .nuCofiber (.shift 1 (.shift 3 .sphere))
        (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) 2 (by decide) xb hxbcycle.2⟩
    have ha3 := desuspendsClass_isCycle
      (D'.classicalSuspension (.shift 3 .sphere)) 2 8 134 sx a3 hdesc' hsx
    have top := finite_zero_extension_8 BHS .nuCofiber (.shift 1 (.shift 3 .sphere))
      (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) ap.top_exponent xb hxbcycle.2
    let y : E2 H SphereSpectrum 11 136 := I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y
    have hycycle : PageRepresentatives.IsCycle H SphereSpectrum 1 (11,136) y := by
      refine ⟨by decide,?_⟩
      rw [PageRepresentatives.cycles_one]
      trivial
    obtain ⟨ys,yt,hys,hyt,hbot⟩ := I'.cofiberInclusion ⟨11,136,[3],[3]⟩ (by simp [Raw.bottomMaps])
    have hys' : ys=y := (Option.some.inj (hys.symm.trans (decode_single .sphere 11 136 3 rfl))).trans (y_basis_label I').symm
    have hyt' : yt=yb := Option.some.inj (hyt.symm.trans hyb)
    have hbot' : adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (11,136) y=yb := by
      change adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (11,136) ys=yt at hbot
      exact (congrArg (fun z : E2 H SphereSpectrum 11 136 =>
        adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) (11,136) z) hys'.symm).trans (hbot.trans hyt')
    have bot := finite_zero_extension_11 BHS .sphere .nuCofiber
      (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) ap.bottom_exponent y hycycle.2
    have bot' : FiniteExtension D' .sphere .nuCofiber
        (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) 2 0 11 136 y yb :=
      (congrArg (fun z : E2 H (HasFunctorialCofiber.cofib D'.hopfAndDetector.nuMap) 11 136 =>
        FiniteExtension D' .sphere .nuCofiber
          (HasFunctorialCofiber.cofibι D'.hopfAndDetector.nuMap) 2 0 11 136 y z) hbot').mp bot
    have he : (normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.f:ℤ)+
        normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.g+
        normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.h=1 := by
      have hf := ap.nu_exponent
      have hg := ap.bottom_exponent
      have hh := ap.top_exponent
      change normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.f=1 at hf
      omega
    have hresult := gmw he (ap.triangle he) 3 0 8 134 a3 y xb yb sx
    have ht := ap.top_exponent
    have hb := ap.bottom_exponent
    have hf := ap.nu_exponent
    change normalizedExponent H D'.hopfAndDetector.nuCofiberTriangle.f=1 at hf
    simp only [hf,hb,ht,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Int.reduceSub,
      Int.reduceToNat,add_zero,sub_zero] at hresult
    have hnc : FiniteExtension.NoCrossing D' .nuCofiber (.shift 1 (.shift 3 .sphere))
        (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap) 3 0 8 134 := by
      rintro ⟨a,b,ha,_,hb,_⟩
      have hnonneg : 0≤(normalizedExponent H (HasFunctorialCofiber.cofibδ D'.hopfAndDetector.nuMap):ℤ) := Nat.cast_nonneg _
      omega
    obtain ⟨_,yy,hyy,hcong⟩ := hresult (by decide) (by decide) (by decide) ha3 hycycle hxbcycle hybper hdesc' top hd' (Or.inl hnc) bot'
    exact ⟨a3,yy,hyy,hcong⟩
  have nu_finite_extension_actual_relation {D' : AdamsComparison H M' Syn}
      (x : E2 H (Sphere 3) 8 133) (y : E2 H SphereSpectrum 11 136)
      (W : KIP126.AdamsSynthetic.FiniteExtensionWitness D' (.shift 3 .sphere) .sphere
        D'.hopfAndDetector.nuMap 4 3 8 133 x y) :
      ∃ (a : BiHom 125 (133 + normalizedExponent H D'.hopfAndDetector.nuMap)
          (XModLambdaN ((extensionSourceObject D' (.shift 3 .sphere) .sphere
            D'.hopfAndDetector.nuMap).obj D'.nu D'.hopfAndDetector) 3))
        (b : BiHom 125 (133 + normalizedExponent H D'.hopfAndDetector.nuMap)
          (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 3)),
        a ≫ finiteExtensionMap D' (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap 3 = b ∧
        Detects (D'.convergence (.quotient 3 (.nu .sphere)))
          (11,136,133+normalizedExponent H D'.hopfAndDetector.nuMap)
          (finiteTargetForExtension D' (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap
            3 3 8 133 W.length_lower y) b := by
    obtain ⟨_,a,b,ha,hb,hab⟩ :=
      (actual_extension_strict_elements _ _ _ _ _ _ _ _).mp W.equation
    refine ⟨_,_,hab,W.target,W.target_rep,b,rfl,?_⟩
    exact hb.symm
  have q3_target_boundary_congruent {D' : AdamsComparison H M' Syn} (BHS : EInftyComparison D')
      (y' y : E2 H SphereSpectrum 11 136)
      (hy : Congruent H SphereSpectrum 3 (11,136) y' y)
      (e : ((D'.family.nuQuotient D'.nu SphereSpectrum 3).sequence.ssData (11,136,134)).eInfty) :
      HasInfinityRepresentative _ 2 (11,136,134) (finiteTargetLabel D' .sphere 3 11 136 2 y') e ↔
        HasInfinityRepresentative _ 2 (11,136,134) (finiteTargetLabel D' .sphere 3 11 136 2 y) e := by
    let c' : cycles H SphereSpectrum ((3:ℤ)-136+(136-(2:ℕ))) (11,136) :=
      ⟨y',by norm_num [cycles_one]⟩
    let c : cycles H SphereSpectrum ((3:ℤ)-136+(136-(2:ℕ))) (11,136) :=
      ⟨y,by norm_num [cycles_one]⟩
    have heq : NestedQuotient.projection _ (boundaries H SphereSpectrum 3 (11,136)) c' =
        NestedQuotient.projection _ (boundaries H SphereSpectrum 3 (11,136)) c := by
      apply sub_eq_zero.mp
      rw [←map_sub,NestedQuotient.projection_eq_zero]
      exact hy.2
    have h1 := BHS.labels.1 .sphere 3 (by decide) (11,136) 2 (by decide) c' e
    have h2 := BHS.labels.1 .sphere 3 (by decide) (11,136) 2 (by decide) c e
    apply h1.trans
    apply Iff.trans _ h2.symm
    exact (congrArg (fun z => BHS.presentation.finiteWindow SphereSpectrum 3 (by decide)
      (11,136) (136-2) (by constructor <;> norm_num) e = z) heq).to_iff
  have detected_map {D' : AdamsComparison H M' Syn}
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
  have q3_nu_map_normalization {D' : AdamsComparison H M' Syn}
      (he : normalizedExponent H D'.hopfAndDetector.nuMap = 1) :
      let A := (SyntheticCategory.biShift
        (0, (normalizedExponent H D'.hopfAndDetector.nuMap : ℤ))).obj
        (D'.nu.functor.obj (Sphere (C:=C) 3))
      let e : A ≅ Smn (Syn:=Syn) 3 4 := by
        dsimp only [A]
        rw [he]
        exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D') ≪≫
          (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
      let Q := D'.quotientFunctoriality.functor 3
      ∀ x : BiHom 125 134 (XModLambdaN A 3),
        x ≫ (finiteExtensionMap D' (.shift 3 .sphere) .sphere D'.hopfAndDetector.nuMap 3) ≫
            (Q.mapIso D'.nu.unitIso).hom =
          (x ≫ (Q.mapIso e).hom) ≫ XModLambdaN.map (normalizedNu D' he) 3 := by
    dsimp only
    let e : (SyntheticCategory.biShift
        (0, (normalizedExponent H D'.hopfAndDetector.nuMap : ℤ))).obj
        (D'.nu.functor.obj (Sphere (C:=C) 3)) ≅ Smn (Syn:=Syn) 3 4 := by
      rw [he]
      exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D') ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
    let Q := D'.quotientFunctoriality.functor 3
    intro x
    change x ≫ Q.map _ ≫ Q.map _ = (x ≫ Q.map e.hom) ≫
      Q.map (e.inv ≫ _ ≫ _)
    simp only [Functor.map_comp, Category.assoc]
    rw [← Q.map_comp_assoc, e.hom_inv_id, Q.map_id, Category.id_comp]
  have nu_relation_weight_transport {D' : AdamsComparison H M' Syn}
      (A : Syn) (g : A ⟶ XModLambdaN (D'.nu.functor.obj SphereSpectrum) 3)
      (n : ℕ) (hn : n=1) (hlower : (n:ℤ)≤3)
      (y : E2 H SphereSpectrum 11 136)
      (h : ∃ (a : BiHom 125 (133+n) A)
        (b : BiHom 125 (133+n) (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 3)),
        a≫g=b ∧ Detects (D'.convergence (.quotient 3 (.nu .sphere))) (11,136,133+n)
          (regradeE2 (A:=D'.family.obj (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 3))
            (i:=(11,136,136-(3-(n:ℤ)).toNat)) (j:=(11,136,133+n))
            (by ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hlower)]; omega)
            (finiteTargetLabel D' .sphere 3 11 136 (3-(n:ℤ)).toNat y)) b) :
      ∃ (a : BiHom 125 134 A)
        (b : BiHom 125 134 (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 3)),
        a≫g=b ∧ Detects (D'.convergence (.quotient 3 (.nu .sphere))) (11,136,134)
          (finiteTargetLabel D' .sphere 3 11 136 2 y) b := by
    subst n
    exact h
  have finite_target_label_to_sphere {D' : AdamsComparison H M' Syn} (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) = D'.quotientLabel q s t k x := by
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      exact (D'.quotientFunctoriality.functor q).mapIso D'.nu.unitIso |>.inv_hom_id
    calc
      _ = familyPageMap D'.family f 2 (s,t,t-k)
          (familyPageMap D'.family g 2 (s,t,t-k) (D'.quotientLabel q s t k x)) :=
        congrArg (fun z => familyPageMap D'.family f 2 (s,t,t-k) z)
          (sphere_quotient_label_to_nu (D':=D') q k s t x).symm
      _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k x) :=
        ConcreteCategory.congr_hom (family_page_comp (D':=D') g f 2 (s,t,t-k)) _
      _ = D'.quotientLabel q s t k x := by
        rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-k) ↑(2-2:ℤ).toNat) _
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_unique ha hb
  have represents_zero_iff_boundary {H : Mod2EilenbergMacLane (C:=C)} (X : C) (r : ℤ) (hr : 2≤r)
      (p : ℤ×ℤ) (x : PageRepresentatives.Ambient H X p) :
      RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x 0 ↔
        x ∈ PageRepresentatives.boundaries H X (r-1) p := by
    let P := (adamsTowerInternalSpectralSequence H.unit X).ssData p
    let n : WithTop ℕ := ↑(r-2).toNat
    have hidx : r-1-1=r-2 := by omega
    constructor
    · rintro ⟨_,z,hz,hzr⟩
      change P.pageπ n z=0 at hzr
      obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) z).mp hzr
      change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1-1).toNat p).hom b=x
      rw [hidx]
      refine ⟨b,?_⟩
      rw [←hz,←hb]
      change (Subobject.ofLE (P.B n) (P.Z 0) _ ≫ P.pageπ 0) b =
        (Subobject.ofLE (P.Z n) (P.Z 0) _ ≫ P.pageπ 0)
          ((Subobject.ofLE (P.B n) (P.Z n) _) b)
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    · intro hx
      change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1-1).toNat p).hom b=x at hx
      rw [hidx] at hx
      obtain ⟨b,hb⟩ := hx
      refine ⟨hr,(Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) b,?_,?_⟩
      · change (Subobject.ofLE (P.Z n) (P.Z 0) _ ≫ P.pageπ 0)
          ((Subobject.ofLE (P.B n) (P.Z n) _) b)=x
        rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
        exact hb
      · change P.pageπ n ((Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) b)=0
        rw [←CategoryTheory.comp_apply]
        change (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n) ≫
          cokernel.π (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n))) b=0
        rw [cokernel.condition]
        rfl
  have nu_three_y_infinity_nonzero {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (I' : AdamsComputationTheorems D' L' G) (SF : Derived.SphereFacts I'.interpretation)
      (b : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3))
      (hb : Detects (D'.quotientConvergence 3 (by decide)) (11,136,134)
        (D'.quotientLabel 3 11 136 2 (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)) b) :
      ∃ e, HasInfinityRepresentative (D'.family.quotient (S_0_0:Syn) 3) 2 (11,136,134)
        (D'.quotientLabel 3 11 136 2 (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)) e ∧ e≠0 := by
    obtain ⟨e,he,b',hb',hgr⟩ := hb
    refine ⟨e,he,?_⟩
    intro hezero
    let g := XModLambdaN.map D'.nu.unitIso.inv 3
    have henu := family_infinity_representative_map g (11,136,134) _ _ he
    have hl := sphere_quotient_label_to_nu (D':=D') 3 2 11 136
      (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)
    change familyPageMap D'.family g 2 (11,136,134) _=_ at hl
    rw [hl,hezero,map_zero] at henu
    let cy : PageRepresentatives.cycles H SphereSpectrum ((3:ℤ)-136+(136-(2:ℕ))) (11,136) :=
      ⟨I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y,by norm_num [PageRepresentatives.cycles_one]⟩
    have hq := (BHS.labels.1 .sphere 3 (by decide) (11,136) 2 (by decide) cy 0).mp henu
    rw [map_zero] at hq
    have hb3 := (NestedQuotient.projection_eq_zero cy).mp hq.symm
    have hb4 : I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y ∈
        PageRepresentatives.boundaries H SphereSpectrum 4 (11,136) :=
      PageRepresentatives.boundaries_monotone H SphereSpectrum (11,136) (by decide : (3:ℤ)≤4) hb3
    have hz := (represents_zero_iff_boundary (H:=H) SphereSpectrum 5 (by decide)
      (11,136) (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)).mpr hb4
    obtain ⟨z,hz',hzn⟩ := SF.y_to_e5
    exact hzn (represents_unique hz' hz)
  have nu_three_actual_map_relation {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (A : MayContext Syn) (I' : AdamsComputationTheorems D' L' G)
      (ap : NuCofiberNormalization D')
      (gmw : KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D' D'.hopfAndDetector.nuCofiberTriangle 0)
      (hd : Derived.CnuDifferential I'.interpretation) (SF : Derived.SphereFacts I'.interpretation) :
      ∃ (a : BiHom 125 134 (XModLambdaN (Smn (Syn:=Syn) 3 4) 3))
        (b : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3)),
        a≫XModLambdaN.map (normalizedNu D' ap.nu_exponent) 3=b ∧
        FiniteDetected D' 3 (by decide) 11 136 2
          (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) b := by
    obtain ⟨x,y',⟨W⟩,hy'⟩ := cnu_mahowald_finite BHS A I' ap gmw hd
    have hw := nu_finite_extension_actual_relation x y' W
    obtain ⟨a,b,hab,hb⟩ := nu_relation_weight_transport _ _ _ ap.nu_exponent W.length_lower y' hw
    obtain ⟨et,het,bt,hbt,hgr⟩ := hb
    have hbY : Detects (D'.convergence (.quotient 3 (.nu .sphere))) (11,136,134)
        (finiteTargetLabel D' .sphere 3 11 136 2
          (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)) b :=
      ⟨et,(q3_target_boundary_congruent BHS _ _ hy' et).mp het,bt,hbt,hgr⟩
    let S := (SyntheticCategory.biShift
        (0,(normalizedExponent H D'.hopfAndDetector.nuMap:ℤ))).obj
        (D'.nu.functor.obj (Sphere (C:=C) 3))
    let e : S ≅ Smn (Syn:=Syn) 3 4 := by
      dsimp only [S]
      rw [ap.nu_exponent]
      exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D') ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
    let Q := D'.quotientFunctoriality.functor 3
    refine ⟨a≫(Q.mapIso e).hom,b≫(Q.mapIso D'.nu.unitIso).hom,?_,?_⟩
    · refine (q3_nu_map_normalization ap.nu_exponent a).symm.trans ?_
      simpa only [Category.assoc] using
        (congrArg (fun z => z≫(Q.mapIso D'.nu.unitIso).hom) hab)
    · have hh := detected_map (.quotient 3 (.nu .sphere)) (.quotient 3 .sphere)
        (Q.mapIso D'.nu.unitIso).hom (11,136,134) _ b hbY
      have hl := finite_target_label_to_sphere (D':=D') 3 2 11 136
        (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)
      change familyPageMap D'.family (Q.mapIso D'.nu.unitIso).hom 2 (11,136,134) _=_ at hl
      have hfinal := (congrArg (fun z : (D'.family.obj (XModLambdaN (S_0_0 : Syn) 3)).E₂ (11,136,134) =>
        Detects (D'.convergence (.quotient 3 .sphere)) (11,136,134) z
          (b≫(Q.mapIso D'.nu.unitIso).hom)) hl).mp hh
      exact ⟨hfinal,nu_three_y_infinity_nonzero BHS I' SF _ hfinal⟩
  have finite_sphere_zero_of_classical_quotient {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t w : ℤ)
      (hw : 0≤t-w ∧ t-w<q)
      (hc : Subsingleton (CycleQuotient H SphereSpectrum ((q:ℤ)-t+w) (1+t-w) (s,t))) :
      IsZero (((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,w)).eInfty) := by
    let e := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) w hw
    haveI := hc
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom q)).eInftyMap (s,t,w)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv q)).eInftyMap (s,t,w)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have nu_three_x_gap {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (a : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a := by
    apply (D'.quotientConvergence 3 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      9 11 122 130 (by decide)
    intro j hj hj'
    have hc : Subsingleton (E2 H SphereSpectrum j (122+j)) := by
      have hjs : j=9 ∨ j=10 := by omega
      rcases hjs with rfl|rfl
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,9,131,[]⟩ (by
          exact List.mem_of_getElem? (i := 170) (by rfl))
        change E2 H SphereSpectrum 9 131 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,10,132,[]⟩ (by
          exact List.mem_of_getElem? (i := 179) (by rfl))
        change E2 H SphereSpectrum 10 132 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
    haveI := hc
    apply finite_sphere_zero_of_classical_quotient BHS 3 (by decide) j (122+j) 130
      (by constructor <;> omega)
    haveI : Subsingleton (cycles H SphereSpectrum ((3:ℤ)-(122+j)+130) (j,122+j)) := inferInstance
    refine ⟨?_⟩
    rintro ⟨x⟩ ⟨y⟩
    exact congrArg (NestedQuotient.projection _ _) (Subsingleton.elim x y)
  have sphere_quotient_high_filtration_zero {D' : AdamsComparison H M' Syn} (BHS : EInftyComparison D')
      (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
      (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
      (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N z) : z=0 := by
    let O : SyntheticObject := .quotient q .sphere
    have hsep : ∀ z : BiHom m w (O.obj D'.nu D'.hopfAndDetector),
        (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) j z) → z=0 :=
      D'.homotopySeparated O m w
    refine (D'.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
    intro j hj
    let i : Tridegree := (j,m+j,w)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
    have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
    haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
      dsimp only [PageRepresentatives.finiteEInftyModel]
      rw [if_neg hh]
      infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro e
    have he : (D'.family.functor.map g).eInftyMap i e=0 :=
      P.injective (Subsingleton.elim _ _)
    have h := congrArg (fun a=>(D'.family.functor.map f).eInftyMap i a) he
    change ((D'.family.functor.map g).eInftyMap i ≫ (D'.family.functor.map f).eInftyMap i) e=_ at h
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
    simpa only [ConcreteCategory.id_apply,map_zero] using h
  have finite_sphere_detection_exists {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0) :
      ∃ a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) q), FiniteDetected D' q hq s t 0 x a := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-0)
      (by constructor <;> omega)
    let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
      ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
    let e := P.symm (NestedQuotient.projection _ _ y)
    have he : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-0)
        (finiteTargetLabel D' .sphere q s t 0 x) e := by
      apply (BHS.labels.1 .sphere q hq (s,t) 0 hq y e).mpr
      exact P.apply_symm_apply _
    have en : e≠0 := by
      intro hz
      have hp := congrArg P hz
      change P (P.symm _)=P 0 at hp
      rw [P.apply_symm_apply,map_zero] at hp
      have hm := (NestedQuotient.projection_eq_zero y).mp hp
      have hb : (1:ℤ)+t-(t-0)=1 := by omega
      change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
      rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
      exact hne hm
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hfg : f≫g=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.hom_inv_id,D'.quotientFunctoriality.map_id]
    let e' := (D'.family.functor.map f).eInftyMap (s,t,t-0) e
    have hel : familyPageMap D'.family f 2 (s,t,t-0) (finiteTargetLabel D' .sphere q s t 0 x)=D'.quotientLabel q s t 0 x := by
      rw [←sphere_quotient_label_to_nu (D':=D') q 0 s t x]
      calc
        _ = familyPageMap D'.family (g≫f) 2 (s,t,t-0) (D'.quotientLabel q s t 0 x) :=
          ConcreteCategory.congr_hom (family_page_comp (D':=D') g f 2 (s,t,t-0)) _
        _ = D'.quotientLabel q s t 0 x := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-0) ↑(2-2:ℤ).toNat) _
    have he' : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
        (D'.quotientLabel q s t 0 x) e' := by
      have hh := family_infinity_representative_map f (s,t,t-0) _ _ he
      rw [hel] at hh
      exact hh
    have en' : e'≠0 := by
      intro hz
      apply en
      have hh := congrArg (fun a=>(D'.family.functor.map g).eInftyMap (s,t,t-0) a) hz
      change ((D'.family.functor.map f).eInftyMap (s,t,t-0) ≫ (D'.family.functor.map g).eInftyMap (s,t,t-0)) e=_ at hh
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hfg,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
      simpa only [ConcreteCategory.id_apply,map_zero] using hh
    exact detection_exists_of_infinity (D':=D') (D'.quotientConvergence q hq) (s,t,t-0) _ e' he' en'
  have finite_sphere_frame {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (c : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
      (hframe : ∀ y : PageRepresentatives.CycleQuotient H SphereSpectrum
          ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
        y=0 ∨ y=NestedQuotient.projection _ _ c) :
      ∀ e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
          (D'.quotientLabel q s t k c.val) e := by
    intro e
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq : (D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k) ≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    rcases hframe (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)) with hz|hz
    · left
      have hzero : (D'.family.functor.map g).eInftyMap (s,t,t-k) e=0 :=
        P.injective (hz.trans (map_zero P).symm)
      rw [hzero,map_zero] at heq
      exact heq.symm
    · right
      have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hz
      have hl : familyPageMap D'.family f 2 (s,t,t-k)
          (finiteTargetLabel D' .sphere q s t k c.val)=D'.quotientLabel q s t k c.val := by
        rw [←sphere_quotient_label_to_nu (D':=D') q k s t c.val]
        calc
          _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k c.val) :=
            ConcreteCategory.congr_hom (family_page_comp (D':=D') g f 2 (s,t,t-k)) _
          _ = D'.quotientLabel q s t k c.val := by
            rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
            exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
              (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
              (s,t,t-k) ↑(2-2:ℤ).toNat) _
      have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
      rw [hl,heq] at h
      exact h
  have finite_detection_peel {D' : AdamsComparison H M' Syn}
      (q : ℕ) (hq : 0<q) (i : Tridegree)
      (x : (D'.family.quotient (S_0_0 : Syn) q).E₂ i)
      (hframe : ∀ e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData i).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 i x e)
      (c : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
      (hc : Detects (D'.quotientConvergence q hq) i x c)
      (a : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a) :
      ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (i.1+1)
        (a-(if b then c else 0)) := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) q)
    have ham : a ∈ (ModuleCat.subobjectModule
        (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (i.2.1-i.1,i.2.2)))
        (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let gr := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
    let e := ((D'.quotientConvergence q hq).identification i).inv gr
    have he : ((D'.quotientConvergence q hq).identification i).hom e=gr :=
      ConcreteCategory.congr_hom ((D'.quotientConvergence q hq).identification i).inv_hom_id gr
    rcases hframe e with he0|hex
    · refine ⟨false,?_⟩
      simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
      have hzero : Detects (D'.quotientConvergence q hq) i 0 a := by
        refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,a',ha',?_⟩
        rw [he0] at he
        exact he
      exact detects_zero_filtration (D'.quotientConvergence q hq) i hzero
    · refine ⟨true,?_⟩
      simp only [↓reduceIte]
      have hax : Detects (D'.quotientConvergence q hq) i x a := ⟨e,hex,a',ha',he⟩
      exact detects_sub_filtration (D'.quotientConvergence q hq) i hax hc
  have finite_sphere_outside_zero {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t w : ℤ)
      (hw : ¬(0≤t-w ∧ t-w<q)) :
      IsZero (((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,w)).eInfty) := by
    let P := BHS.presentation.finite SphereSpectrum q hq (s,t) w
    haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q (s,t) w) := by
      dsimp only [PageRepresentatives.finiteEInftyModel]
      rw [if_neg hw]
      infer_instance
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
      P.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom q)).eInftyMap (s,t,w)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv q)).eInftyMap (s,t,w)
    have hfg : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,comp_zero])
  have finite_sphere_filtration_floor {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (m w N : ℤ)
      (hN : 0≤N) (hNW : m+N≤w)
      (a : BiHom m w (XModLambdaN (S_0_0 : Syn) q)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N a := by
    apply ((D'.quotientConvergence q hq).filtrationAtLeast_iff_of_eInfty_isZero
      0 N m w hN ?_ a).mp
    · change ∃ z, towerHomotopyMap (nuCoefficientUnit H.unit D'.nu)
        (XModLambdaN (S_0_0 : Syn) q) 0 (m,w) z=a
      refine ⟨a,?_⟩
      change a≫adamsTowerMap (nuCoefficientUnit H.unit D'.nu)
        (XModLambdaN (S_0_0 : Syn) q) 0 0 _=a
      rw [adamsTowerMap_self]
      exact Category.comp_id a
    · intro j hj hjN
      exact finite_sphere_outside_zero BHS q hq j (m+j) w (by omega)
  have nu_x_label {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 8 130 (X) = I'.interpretation.basis .sphere 8 130 0 := by
    have hc := I'.monomials (⟨.sphere,8,130,["1,1,323,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 158) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (X)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩ * generator ⟨323,by decide⟩ = projection (monomialOfString "1,1,323,1")
      have hs : "1,1,323,1" ≠ "" := by decide
      have hp : (("1,1,323,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 323, 1] := by
        have split : "1,1,323,1".splitOn "," = ["1", "1", "323", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have nu_three_nonzero_detects_x {D' : AdamsComparison H M' Syn}
      (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') (SF : Derived.SphereFacts I'.interpretation)
      (a : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3)) (han : a≠0) :
      FiniteDetected D' 3 (by decide) 8 130 0 (I'.interpretation.sphere 8 130 X) a := by
    obtain ⟨xr,hxr,hxn⟩ := SF.x_to_e6
    have hX5 : I'.interpretation.sphere 8 130 X ∈ PageRepresentatives.cycles H SphereSpectrum 5 (8,130) :=
      ((PageRepresentatives.isCycle_iff_represents H SphereSpectrum 6 (by decide) (8,130)
        (I'.interpretation.sphere 8 130 X)).mpr ⟨xr,hxr⟩).2
    have hX3 := PageRepresentatives.cycles_antitone H SphereSpectrum (8,130) (by decide : (3:ℤ)≤5) hX5
    have hXn : I'.interpretation.sphere 8 130 X≠0 := by
      intro h
      rw [h] at hxr
      exact hxn (represents_unique hxr
        (RepresentsOnPage.zero (by decide : (2:ℤ)≤6)))
    obtain ⟨x3,hx3⟩ := finite_sphere_detection_exists BHS 3 (by decide) 8 130 _ hX3 hXn
    change BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3) at x3
    let c : PageRepresentatives.cycles H SphereSpectrum ((3:ℤ)-130+(130-0)) (8,130) :=
      ⟨I'.interpretation.sphere 8 130 X,hX3⟩
    have frame : ∀ z : PageRepresentatives.CycleQuotient H SphereSpectrum 3 1 (8,130),
        z=0 ∨ z=NestedQuotient.projection _ _ c := by
      obtain ⟨e,he⟩ := I'.basis ⟨.sphere,8,130,["1,1,323,1"]⟩ (by
        exact List.mem_of_getElem? (i := 158) (by rfl))
      change E2 H SphereSpectrum 8 130 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
      have hb : e.symm (Finsupp.single (0:Fin 1) 1)=I'.interpretation.sphere 8 130 X := by
        rw [nu_x_label I']
        exact he 0
      rintro ⟨z⟩
      have hh : e z.val=Finsupp.single 0 (e z.val 0) := by
        apply Finsupp.ext
        intro i
        fin_cases i
        simp
      have hz : z.val=e.symm (Finsupp.single 0 (e z.val 0)) := by
        rw [←hh,LinearEquiv.symm_apply_apply]
      generalize hc : e z.val 0=d at hz
      fin_cases d
      · change z.val=e.symm (Finsupp.single 0 (0:F2)) at hz
        simp only [Finsupp.single_zero,map_zero] at hz
        left
        exact (NestedQuotient.projection_eq_zero z).mpr (hz ▸ (PageRepresentatives.boundaries H SphereSpectrum 1 (8,130)).zero_mem)
      · change z.val=e.symm (Finsupp.single 0 (1:F2)) at hz
        right
        have heq : z=c := Subtype.ext (hz.trans hb)
        exact congrArg (NestedQuotient.projection _ _) heq
    have hinf := finite_sphere_frame BHS 3 0 (by decide) (by decide) 8 130 c frame
    have ha8 := finite_sphere_filtration_floor BHS 3 (by decide) 122 130 8 (by decide) (by decide) a
    obtain ⟨b,hb⟩ := finite_detection_peel 3 (by decide) (8,130,130)
      (D'.quotientLabel 3 8 130 0 (I'.interpretation.sphere 8 130 X)) hinf x3 hx3.1 a ha8
    have heq : a-(if b then x3 else 0)=0 := by
      apply sphere_quotient_high_filtration_zero BHS 3 (by decide) 122 130 11 (by decide)
      exact (nu_three_x_gap I' BHS _).mp hb
    cases b
    · simp only [Bool.false_eq_true,↓reduceIte,sub_zero] at heq
      exact (han heq).elim
    · simp only [↓reduceIte] at heq
      rw [sub_eq_zero.mp heq]
      exact hx3
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have shiftSwap_add (coh : BiShiftCoherence Syn)
      (a b c : ℤ × ℤ) (A : Syn) :
      (shiftSwap a (b+c) A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
      (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    let habc : (a+b)+c=a+(b+c) := add_assoc a b c
    let hbac : b+(a+c)=a+(b+c) := by abel
    have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
    have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
      (add_comm _ _) rfl habc hbac A
    have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
      rfl (add_comm _ _) (add_comm _ _) hbac A
    simp only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    rw [Functor.map_comp]
    apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
      ((SyntheticCategory.biShift a).obj A))).mp
    simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← h₁]
    simp only [Category.assoc]
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
    -- Cancel the common left factor introduced by the first associativity square.
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
    rw [← Category.assoc,h₂]
    simp only [Category.assoc]
    apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
      ((SyntheticCategory.biShift b).obj A))).mpr
    apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
      ((SyntheticCategory.biShift b).obj A))).mp
    rw [← Category.assoc,← Category.assoc,← h₃]
    simp only [Category.assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
    rfl
  have shiftSwap_add_eq (coh : BiShiftCoherence Syn)
      (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
      (shiftSwap a d A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
      (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    subst d
    exact shiftSwap_add coh a b c A
  have shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
        (shiftSwap a b B).hom =
      (shiftSwap a b A).hom ≫
        (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
    exact ((biShiftAddIso a b (a+b) rfl) ≪≫
      (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f
  have shiftSwap_hom_eq (a b d : ℤ × ℤ)
      (hab : a+b=d) (hba : b+a=d) (A : Syn) :
      (shiftSwap a b A).hom =
        (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
    subst d
    rfl
  have lambda_pow_shift (coh : BiShiftCoherence Syn)
      (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
      lambdaPow n ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow n A) := by
    induction n generalizing A with
    | zero =>
      change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a 0 A).hom ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
      have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
          (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
            (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
              (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
        rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
        exact (coh.right_unit a A).symm
      rw [shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
      exact h
    | succ n ih =>
      have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
            (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
        rw [lambdaPow_one coh,lambdaPow_one coh]
        change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
        rw [shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
        exact coh.lambda_comm a A
      have hn := shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
      have hh := shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
        (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
      change (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
          (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
        (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
          (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
      rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
        lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
      simp only [Functor.map_comp,Category.assoc]
      rw [reassoc_of% hn]
      rw [reassoc_of% hh]
      rfl
  have quotient_shift_iso (D' : AdamsComparison H M' Syn) (a : ℤ × ℤ) (A : Syn) (q : ℕ) :
      ∃ e : (SyntheticCategory.biShift a).obj (XModLambdaN A q) ≅
        XModLambdaN ((SyntheticCategory.biShift a).obj A) q,
        (SyntheticCategory.biShift a).map (XModLambdaN.incl A q) ≫ e.hom =
        XModLambdaN.incl ((SyntheticCategory.biShift a).obj A) q := by
    letI := D'.shiftCommShift a
    letI := D'.shiftExact a
    let T := Triangle.mk (lambdaPow q A)
      (HasFunctorialCofiber.cofibι (lambdaPow q A))
      (HasFunctorialCofiber.cofibδ (lambdaPow q A))
    let U := Triangle.mk (lambdaPow q ((SyntheticCategory.biShift a).obj A))
      (HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
      (HasFunctorialCofiber.cofibδ (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
    let c : ((SyntheticCategory.biShift a).mapTriangle.obj T).obj₁ ≅ U.obj₁ :=
      (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).symm
    have hc : ((SyntheticCategory.biShift a).mapTriangle.obj T).mor₁ ≫ (Iso.refl _).hom =
        c.hom ≫ U.mor₁ := by
      change (SyntheticCategory.biShift a).map (lambdaPow q A) ≫ 𝟙 _ =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).inv ≫
          lambdaPow q ((SyntheticCategory.biShift a).obj A)
      rw [lambda_pow_shift D'.shiftCoherence]
      simp only [Iso.inv_hom_id_assoc,Category.comp_id]
    let E := CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂
      ((SyntheticCategory.biShift a).mapTriangle.obj T) U
      ((SyntheticCategory.biShift a).map_distinguished T (HasFunctorialCofiber.cofib_distinguished _))
      (HasFunctorialCofiber.cofib_distinguished _) c (Iso.refl _) hc
    refine ⟨Triangle.π₃.mapIso E, ?_⟩
    have hh : (SyntheticCategory.biShift a).map (HasFunctorialCofiber.cofibι (lambdaPow q A)) ≫
        E.hom.hom₃ = E.hom.hom₂ ≫
        HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)) := E.hom.comm₂
    have he₂ : E.hom.hom₂ = 𝟙 _ :=
      CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
    rw [he₂,Category.id_comp] at hh
    exact hh
  have q3_sphere_shift_transport (D' : AdamsComparison H M' Syn) :
      ∃ κ : XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3),
        XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3 ≫ κ.hom =
          (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:Syn) 3) ∧
        ∀ x : BiHom 125 134 (XModLambdaN (Smn (Syn:=Syn) 3 4) 3),
          (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:Syn) 3)).symm
            (x ≫ κ.hom) = 0 ↔ x = 0 := by
    obtain ⟨e, he⟩ := quotient_shift_iso D' (3,4) (S_0_0:Syn) 3
    refine ⟨e.symm, ?_, ?_⟩
    · change XModLambdaN.incl ((SyntheticCategory.biShift (3,4)).obj (S_0_0:Syn)) 3 ≫ e.inv = _
      have hh := congrArg (fun f => f ≫ e.inv) he
      simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] using hh.symm
    · intro x
      let E := (biHomTargetIso 125 134 e.symm).trans
        (suspInvarianceAddEquiv 122 130 3 4 (XModLambdaN (S_0_0:Syn) 3)).symm
      exact E.map_eq_zero_iff
  have detects_nonzero_homotopy_ne_zero {D' : AdamsComparison H M' Syn}
      {A : Syn} (c : TowerConvergence (nuCoefficientUnit H.unit D'.nu) D'.family A)
      (i : Tridegree) (x : (D'.family.obj A).E₂ i) (a : BiHom (i.2.1-i.1) i.2.2 A)
      (h : DetectsNonzero c i x a) : a≠0 := by
    obtain ⟨⟨e,he,a',ha',hgr⟩,e',he',hn⟩ := h
    have hee := he.unique he'
    intro hz
    have ha0 : a'=0 := (ModuleCat.mono_iff_injective _).mp inferInstance
      ((ha'.trans hz).trans (map_zero _).symm)
    have he0 : e=0 := (ModuleCat.mono_iff_injective _).mp inferInstance (by
      rw [hgr,ha0,map_zero,map_zero])
    exact hn (hee.symm.trans he0)
  have nu_three_transported_relation {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (A : MayContext Syn) (I' : AdamsComputationTheorems D' L' G)
      (ap : NuCofiberNormalization D')
      (gmw : KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D' D'.hopfAndDetector.nuCofiberTriangle 0)
      (hd : Derived.CnuDifferential I'.interpretation) (SF : Derived.SphereFacts I'.interpretation) :
      ∃ κ : XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0 : Syn) 3),
        XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3≫κ.hom =
          (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0 : Syn) 3) ∧
      ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3))
        (y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3)),
        FiniteDetected D' 3 (by decide) 8 130 0 (I'.interpretation.sphere 8 130 X) x ∧
        FiniteDetected D' 3 (by decide) 11 136 2 (I'.interpretation.sphere 11 136 Y) y ∧
        ((susp_invariance 122 130 3 4 (XModLambdaN (S_0_0 : Syn) 3)) x)≫κ.inv≫
          XModLambdaN.map (normalizedNu D' ap.nu_exponent) 3=y := by
    obtain ⟨a,b,hab,hb⟩ := nu_three_actual_map_relation BHS A I' ap gmw hd SF
    have hbn : b≠0 := detects_nonzero_homotopy_ne_zero _ _ _ _ hb
    have han : a≠0 := by
      intro hz
      exact hbn (hab.symm.trans (by rw [hz,zero_comp]))
    obtain ⟨κ,hκ,hκn⟩ := q3_sphere_shift_transport D'
    let x := (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0 : Syn) 3)).symm (a≫κ.hom)
    have hxn : x≠0 := by
      intro hz
      exact han ((hκn a).mp hz)
    have hx := nu_three_nonzero_detects_x I' BHS SF x hxn
    refine ⟨κ,hκ,x,b,hx,hb,?_⟩
    have he : (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0 : Syn) 3)) x=a≫κ.hom :=
      Equiv.apply_symm_apply _ _
    rw [he,Category.assoc,κ.hom_inv_id_assoc]
    exact hab
  have huq : ∀u v:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3),u≠0→v≠0→u=v := by
   intro u v hu hv
   apply sub_eq_zero.mp
   apply sphere_quotient_high_filtration_zero BHS 3 (by decide) 122 130 11 (by decide)
   apply (nu_three_x_gap I' BHS (u-v)).mp
   exact detects_sub_filtration (D'.quotientConvergence 3 (by decide)) (8,130,130)
     (nu_three_nonzero_detects_x I' BHS SF u hu).1
     (nu_three_nonzero_detects_x I' BHS SF v hv).1
  obtain ⟨κ,hκ,x,y,hx,hy,hxy⟩:=nu_three_transported_relation BHS A I' ap gmw hd SF
  exact ⟨huq,κ,hκ,x,y,detects_nonzero_homotopy_ne_zero _ _ _ _ hx,hx,hy,hxy⟩

end
end NuThreeActualProof

section NuThreeActionProof

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}

open KIP126.Literature.AdamsSynthetic

set_option maxHeartbeats 8000000 in
private theorem q3_sphere_action_actual_map
    (D':AdamsComparison H M' Syn) (BHS:EInftyComparison D')
    (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (may:MayContext Syn)
    (unique:∀u v:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3))
    (hκ:XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3≫κ.hom=
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:Syn) 3))
    (ν:BiHom 3 4 (S_0_0:Syn))
    (x:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3)) (hx:x≠0) :
    sphereAction ν x=(susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:Syn) 3) x)≫
      κ.inv≫XModLambdaN.map ν 3 := by
  classical
  have sphere_quotient_high_filtration_zero {D' : AdamsComparison H M' Syn} (BHS : EInftyComparison D')
      (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
      (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
      (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N z) : z=0 := by
    let O : SyntheticObject := .quotient q .sphere
    have hsep : ∀ z : BiHom m w (O.obj D'.nu D'.hopfAndDetector),
        (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) j z) → z=0 :=
      D'.homotopySeparated O m w
    refine (D'.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
    intro j hj
    let i : Tridegree := (j,m+j,w)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
    have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
    haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
      dsimp only [PageRepresentatives.finiteEInftyModel]
      rw [if_neg hh]
      infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro e
    have he : (D'.family.functor.map g).eInftyMap i e=0 :=
      P.injective (Subsingleton.elim _ _)
    have h := congrArg (fun a=>(D'.family.functor.map f).eInftyMap i a) he
    change ((D'.family.functor.map g).eInftyMap i ≫ (D'.family.functor.map f).eInftyMap i) e=_ at h
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
    simpa only [ConcreteCategory.id_apply,map_zero] using h
  have tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=Syn) m n)).Faithful := by
    let e : Smn (Syn:=Syn) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ Syn) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:Syn) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:Syn)
    let f : tensorLeft (Smn (Syn:=Syn) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 Syn :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft Syn).mapIso e ≪≫ leftUnitorNatIso Syn
    exact Functor.Faithful.of_comp_iso f
  let tensorLeft_sphere_fullyFaithful (m n:ℤ) : (tensorLeft (Smn (Syn:=Syn) m n)).FullyFaithful := by
    let e : Smn (Syn:=Syn) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ Syn) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:Syn) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:Syn)
    let f : tensorLeft (Smn (Syn:=Syn) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 Syn :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft Syn).mapIso e ≪≫ leftUnitorNatIso Syn
    letI := tensorLeft_sphere_faithful (-m) (-n)
    exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.ofFullyFaithful (𝟭 Syn)).ofIso f.symm)
  have lambda_cubed_kills_unit_hom (D':AdamsComparison H M' Syn)
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (may:MayContext Syn)
      (f:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 3) :
      lambdaPow 3 (S_0_0:Syn)≫f=0 := by
    letI:=algebra.syntheticSymmetric
    letI:=may.leftShift
    letI:=may.leftExact
    let l:BiHom 0 (-3) (S_0_0:Syn):=lambdaPow 3 (S_0_0:Syn)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:Syn) 3):=SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn)≫f
    have hl:quotientClass 3 l=0 := by
      change lambdaPow 3 (S_0_0:Syn)≫XModLambdaN.incl (S_0_0:Syn) 3=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:Syn) 3) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=qb.sphere_action 3 (by decide) 0 (-3) 0 0 l z
    have hp:KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 3 (by decide)) (quotientClass 3 l) z=0 := by
      rw [hl]
      unfold KIP126.AdamsSynthetic.algebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-3) (XModLambdaN (S_0_0:Syn) 3))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:Syn) 3) ◁ (0:BiHom 0 (-3) (XModLambdaN (S_0_0:Syn) 3))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:Syn) 3)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 3 (S_0_0:Syn)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 3 (S_0_0:Syn))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-3) (0,0)).hom.app (S_0_0:Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=Syn) 0 (-3)):= by
        have hc := D'.shiftCoherence.right_unit (0,-3) (S_0_0:Syn)
        change (biShiftAddIso (0,-3) (0,0) (0,-3) (by decide)).hom.app (S_0_0:Syn)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-3) (0,0)).inv.app (S_0_0:Syn)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=Syn) 0 (-3))≫lambdaPow 3 (S_0_0:Syn))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
      (D':AdamsComparison H M' Syn) (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (may:MayContext Syn) :
      Function.Surjective (fun g:XModLambdaN (S_0_0:Syn) 3⟶XModLambdaN (S_0_0:Syn) 3 =>
        XModLambdaN.incl (S_0_0:Syn) 3≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:Syn) 3
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_cubed_kills_unit_hom D' algebra qb may f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective {D' : AdamsComparison H M' Syn} (BHS:EInftyComparison D') :
      Function.Injective (fun g:XModLambdaN (S_0_0:Syn) 3⟶XModLambdaN (S_0_0:Syn) 3 =>
        XModLambdaN.incl (S_0_0:Syn) 3≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:Syn) 3≫f=XModLambdaN.incl (S_0_0:Syn) 3≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:Syn) 3
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:Syn) 3≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=Syn) 1 (-3):=(biSuspensionIso 3 (S_0_0:Syn)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero BHS 3 (by decide) 1 (-3) 0 (by decide)
      change ∃a,towerHomotopyMap (nuCoefficientUnit H.unit D'.nu)
        (XModLambdaN (S_0_0:Syn) 3) 0 (1,-3) a=e.inv≫δ
      refine ⟨e.inv≫δ,?_⟩
      change _≫adamsTowerMap (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0:Syn) 3) 0 0 _=_
      rw [adamsTowerMap_self]
      exact Category.comp_id _
    have hd:δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd,comp_zero] using hδ
  have extend_unit_iso
      {S A:Syn} (i:S⟶A)
      (hi:Function.Bijective (fun g:A⟶A=>i≫g))
      (F T:Syn⥤Syn) (ff:F.FullyFaithful) (tt:T.FullyFaithful)
      (eS:F.obj S≅T.obj S) (eA:F.obj A≅T.obj A) :
      ∃E:F.obj A≅T.obj A,F.map i≫E.hom=eS.hom≫T.map i := by
    have lift (F T:Syn⥤Syn) (ff:F.FullyFaithful)
        (eA:F.obj A≅T.obj A) (f:F.obj S⟶T.obj A) :
        ∃g:F.obj A⟶T.obj A,F.map i≫g=f := by
      let z:=ff.preimage (f≫eA.inv)
      obtain ⟨g,hg⟩:=hi.2 z
      change i≫g=z at hg
      refine ⟨F.map g≫eA.hom,?_⟩
      rw [←Category.assoc,←F.map_comp,hg]
      have hz:F.map z=f≫eA.inv:=ff.map_preimage _
      rw [hz,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    have inj (F:Syn⥤Syn) (ff:F.FullyFaithful)
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
  have q3_unit_tensor_iso
      (D':AdamsComparison H M' Syn) (BHS:EInftyComparison D')
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (may:MayContext Syn) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3) ≅
          Smn (Syn:=Syn) 3 4 ⊗ XModLambdaN (S_0_0:Syn) 3,
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:Syn) 3)≫e.hom=
          (ρ_ (Smn (Syn:=Syn) 3 4)).inv≫(𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:Syn) 3) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:Syn) 3)
      ⟨unit_restriction_injective BHS,unit_restriction_surjective D' algebra qb may⟩
      (SyntheticCategory.biShift (3,4)) (tensorLeft (Smn (Syn:=Syn) 3 4))
      (SyntheticCategory.biShift_fullyFaithful (3,4)) (tensorLeft_sphere_fullyFaithful 3 4)
      (ρ_ (Smn (Syn:=Syn) 3 4)).symm (biShift_eq_tensor_Smn 3 4 (XModLambdaN (S_0_0:Syn) 3))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q3_pi_four_one_zero {D' : AdamsComparison H M' Syn} (BHS : EInftyComparison D')
      (z : BiHom 4 1 (XModLambdaN (S_0_0:Syn) 3)) : z=0 := by
    apply sphere_quotient_high_filtration_zero BHS 3 (by decide) 4 1 0 (by decide) z
    change ∃ a, towerHomotopyMap (nuCoefficientUnit H.unit D'.nu)
      (XModLambdaN (S_0_0:Syn) 3) 0 (4,1) a=z
    refine ⟨z,?_⟩
    change z≫adamsTowerMap (nuCoefficientUnit H.unit D'.nu)
      (XModLambdaN (S_0_0:Syn) 3) 0 0 _=z
    rw [adamsTowerMap_self]
    exact Category.comp_id z
  have q3_sphere_inclusion_hom_injective {D' : AdamsComparison H M' Syn} (BHS : EInftyComparison D') :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ⟶
        XModLambdaN (S_0_0:Syn) 3 => XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3 ≫ f =
      XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=Syn) 3 4) 3
    have hT : T ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=Syn) 4 1 :=
      (biSuspensionIso 3 (Smn (Syn:=Syn) 3 4)).symm ≪≫
        (SyntheticCategory.biShift_comp (3,4) (1,-3)).app (S_0_0:Syn)
    have he := q3_pi_four_one_zero BHS (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q3_tensor_source_square
      (D':AdamsComparison H M' Syn) (may:MayContext Syn)
      (unique:∀u v:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3) ≅
        Smn (Syn:=Syn) 3 4 ⊗ XModLambdaN (S_0_0:Syn) 3)
      (d:Smn (Syn:=Syn) 125 134 ≅ Smn (Syn:=Syn) 3 4 ⊗ Smn (Syn:=Syn) 122 130)
      (x:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ x)=
        (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:Syn) 3) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=Syn) (3,4)
    let T:=tensorLeft (Smn (Syn:=Syn) 3 4)
    letI:=D'.shiftAdditive (3,4)
    letI:=may.leftShift (Smn (Syn:=Syn) 3 4)
    letI:=may.leftExact (Smn (Syn:=Syn) 3 4)
    letI:T.Faithful:=tensorLeft_sphere_faithful 3 4
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (3,4)
    let c: F.obj (Smn (Syn:=Syn) 122 130) ≅ Smn (Syn:=Syn) 125 134 :=
      (SyntheticCategory.biShift_comp (122,130) (3,4)).app (S_0_0:Syn)
    let z:BiHom 122 130 (XModLambdaN (S_0_0:Syn) 3):=
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
    change d.hom≫(𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q3_algebra_filler
      (D':AdamsComparison H M' Syn) (BHS:EInftyComparison D')
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (may:MayContext Syn)
      (κ:XModLambdaN (Smn (Syn:=Syn) 3 4) 3 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3))
      (hκ:XModLambdaN.incl (Smn (Syn:=Syn) 3 4) 3≫κ.hom=
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:Syn) 3)) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:Syn) 3) ≅
          Smn (Syn:=Syn) 3 4 ⊗ XModLambdaN (S_0_0:Syn) 3,
        letI:=algebra.syntheticSymmetric
        ∀ν:BiHom 3 4 (S_0_0:Syn),
        κ.hom≫e.hom≫(quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 3))≫
          (algebra.quotients.algebra 3 (by decide)).mul=XModLambdaN.map ν 3 := by
    letI:=algebra.syntheticSymmetric
    letI:=algebra.quotients.algebra 3 (by decide)
    obtain ⟨e,he⟩:=q3_unit_tensor_iso D' BHS algebra qb may
    refine ⟨e,?_⟩
    intro ν
    apply q3_sphere_inclusion_hom_injective BHS
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:Syn) 3),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←algebra.quotients.unit 3 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 3 ν)
    change (ρ_ (Smn (Syn:=Syn) 3 4)).inv≫(quotientClass 3 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 3 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 3
  letI:=algebra.syntheticSymmetric
  let Q:=algebra.quotients.algebra 3 (by decide)
  letI:=Q
  letI:=algebra.quotients.commutative 3 (by decide)
  obtain ⟨e,he⟩:=q3_algebra_filler D' BHS algebra qb may κ hκ
  let d:Smn (Syn:=Syn) 125 134 ≅ Smn (Syn:=Syn) 3 4 ⊗ Smn (Syn:=Syn) 122 130 :=
    ((SyntheticCategory.biShift_comp (3,4) (122,130)).app (S_0_0:Syn)).symm ≪≫
      biShift_eq_tensor_Smn 122 130 (Smn (Syn:=Syn) 3 4) ≪≫ β_ (Smn (Syn:=Syn) 122 130) (Smn (Syn:=Syn) 3 4)
  have ht:=q3_tensor_source_square D' may unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:Syn) 3)
  change (β_ (XModLambdaN (S_0_0:Syn) 3) (XModLambdaN (S_0_0:Syn) 3)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 3 ν)≫Q.mul=
      (β_ (Smn (Syn:=Syn) 122 130) (Smn (Syn:=Syn) 3 4)).hom≫
        (quotientClass 3 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 3 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ x)≫(quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 3)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←qb.sphere_action 3 (by decide) 3 4 122 130 ν x]
  change KIP126.AdamsSynthetic.algebraProduct Q (quotientClass 3 ν) x=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=Syn) 3 4) ⊗ₘ x)≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 3))≫Q.mul := by
      dsimp only [KIP126.AdamsSynthetic.algebraProduct,d,Iso.trans_hom,Iso.symm_hom]
      rw [hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:Syn) 3) x)≫e.hom≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 3))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 3))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]
end
end NuThreeActionProof

section NuFiveFromThreeProof
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra KIP126.Literature.AdamsSynthetic KIP126.Computation.SphereAndCofiber
open KIP126.Algebra KIP126.LinE2 PageRepresentatives KIP126.Computation.Near126
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] adamsTowerInternalD adamsTowerSSData KIP126.LinE2.homogeneousPart
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
private theorem nu_five_of_three
    (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') (A : AdamsAlgebraStructures D') (compatibility : AlgebraDetectionCompatibility D' A)
    (SF : Derived.SphereFacts I'.interpretation)
    (nu : BiHom 3 4 (S_0_0 : Syn))
    (hnu : D'.sphereFirstQuotient 1 4 (quotientClass 1 nu)=Sphere.Internal.hi H M' 2)
    (hthree : ∃ x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3),
      ∃ y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3),
      FiniteDetected D' 3 (by decide) 8 130 0 (I'.interpretation.sphere 8 130 X) x ∧
      FiniteDetected D' 3 (by decide) 11 136 2 (I'.interpretation.sphere 11 136 Y) y ∧
      sphereAction nu x=y) :
    NuExtension5 D' (I'.interpretation.sphere 8 130 X) (I'.interpretation.sphere 11 136 Y) nu := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b) : a = b := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_unique ha hb
  have represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a)
      (ht : KIP126.SpectralSequence.ReachesPage E t p x) : E.d r p a = 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_d_zero_of_later hr0 hrt ha ht
  have next_projection_zero_iff_incoming
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
      (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
      (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
        ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ)) :
      (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
        (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
          (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
            (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
          LinearMap.range (E.d r p).hom := by
    exact KIP126.SpectralSequence.FinitePageCalculus.next_projection_zero_iff_incoming E r hr p z
  have represents_before
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
      {x : E.Page 2 p} {xt : E.Page t p}
      (hr : 2 ≤ r) (hrt : r ≤ t) (ht : KIP126.SpectralSequence.RepresentsOnPage E t p x xt) :
      ∃ xr, KIP126.SpectralSequence.RepresentsOnPage E r p x xr := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_before hr hrt ht
  have differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {t : ℤ} {q : ℤ×ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
      (hr0 : E.r₀ ≤ r) (hrt : r < t)
      (h : KIP126.SpectralSequence.HasDifferential E r p q x y) : KIP126.SpectralSequence.RepresentsOnPage E t q y 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.differential_target_later_zero hr0 hrt h
  have represents_add_tail
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
      {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_add_tail hx hy
  have nu_af10_frame (I' : AdamsComputationTheorems D' L' G) :
      ∃ a : (sequence D' .sphere).Page 3 (10,135),
      ∃ b : (sequence D' .sphere).Page 3 (13,137),
        RepresentsOnPage (sequence D' .sphere) 3 (10,135) (I'.interpretation.basis .sphere 10 135 0) a ∧
        RepresentsOnPage (sequence D' .sphere) 3 (13,137) (I'.interpretation.basis .sphere 13 137 0) b ∧
        (sequence D' .sphere).d 3 (10,135) a=b ∧
        ∀ z : (sequence D' .sphere).Page 3 (10,135), z=0 ∨ z=a := by
    let E := sequence D' .sphere
    have h251 : HasDifferential E 2 (8,134) (10,135)
        (I'.interpretation.basis .sphere 8 134 1) (I'.interpretation.basis .sphere 10 135 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
        exact List.mem_of_getElem? (i := 251) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (8,134) (10,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h252 : HasDifferential E 3 (10,135) (13,137)
        (I'.interpretation.basis .sphere 10 135 0) (I'.interpretation.basis .sphere 13 137 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
        exact List.mem_of_getElem? (i := 252) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (10,135) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h253 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 1) (I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
        exact List.mem_of_getElem? (i := 253) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h254 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 2) (I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
        exact List.mem_of_getElem? (i := 254) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h255 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 4) (I'.interpretation.basis .sphere 12 136 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
        exact List.mem_of_getElem? (i := 255) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 10 135 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 4 := he 4
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 12 136 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 4 := hf 4
    obtain ⟨_,a0,b0,ha0,hb0,hd⟩ := h252
    have hd' : E.d 3 (10,135) a0=b0 := hd
    have hz3 : RepresentsOnPage E 3 (10,135) (I'.interpretation.basis .sphere 10 135 3) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h251
    have dz {p : ℤ×ℤ} {x : E.Page 2 p} (hx : ReachesPage E 3 p x) : E.d 2 p x=0 := by
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
      rw [←hb.eq_on_page_two] at hb
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨a,ha⟩
    have hd0 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 0)=0 := dz ⟨a0,ha0⟩
    have hd1 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 1)=
        I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
    have hd2 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 2)=
        I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
    have hd3 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 3)=0 := dz ⟨0,hz3⟩
    have hd4 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 4)=
        I'.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
    have frame (a : E.Page 3 (10,135)) : a=0 ∨ a=a0 := by
      let A := E.ssData (10,135)
      haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance a
      let x : E.Page 2 (10,135) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤1)) ≫ A.pageπ 0) z
      have hxa : RepresentsOnPage E 3 (10,135) x a := ⟨by decide,z,rfl,hza⟩
      have hc : E.d 2 (10,135) x=0 := dz ⟨a,hxa⟩
      have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
        apply Finsupp.ext
        intro i
        fin_cases i <;> simp
      have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
        rw [←heq,LinearEquiv.symm_apply_apply]
      generalize hc0 : e x 0=c0 at hxe
      generalize hc1 : e x 1=c1 at hxe
      generalize hc2 : e x 2=c2 at hxe
      generalize hc3 : e x 3=c3 at hxe
      generalize hc4 : e x 4=c4 at hxe
      fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
        rw [hxe] at hc hxa
        exact Or.inl (represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤3)))
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he4] at hc hxa
        simp only [hd4] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he3] at hc hxa
        exact Or.inl (represents_unique hxa hz3)
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he3, he4] at hc hxa
        simp only [map_add,hd3,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2] at hc hxa
        simp only [hd2] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he4] at hc hxa
        simp only [map_add,hd2,hd4] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he3] at hc hxa
        simp only [map_add,hd2,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he3, he4] at hc hxa
        simp only [map_add,hd2,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1] at hc hxa
        simp only [hd1] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he4] at hc hxa
        simp only [map_add,hd1,hd4] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he3] at hc hxa
        simp only [map_add,hd1,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he3, he4] at hc hxa
        simp only [map_add,hd1,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2] at hc hxa
        simp only [map_add,hd1,hd2] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he4] at hc hxa
        simp only [map_add,hd1,hd2,hd4] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he3] at hc hxa
        simp only [map_add,hd1,hd2,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he3, he4] at hc hxa
        simp only [map_add,hd1,hd2,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0] at hc hxa
        exact Or.inr (represents_unique hxa ha0)
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he4] at hc hxa
        simp only [map_add,hd0,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he3] at hc hxa
        exact Or.inr (by simpa only [add_zero] using represents_unique hxa (represents_add_tail ha0 hz3))
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he3, he4] at hc hxa
        simp only [map_add,hd0,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2] at hc hxa
        simp only [map_add,hd0,hd2,zero_add] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he4] at hc hxa
        simp only [map_add,hd0,hd2,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he3] at hc hxa
        simp only [map_add,hd0,hd2,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he3, he4] at hc hxa
        simp only [map_add,hd0,hd2,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1] at hc hxa
        simp only [map_add,hd0,hd1,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he3] at hc hxa
        simp only [map_add,hd0,hd1,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he3, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2] at hc hxa
        simp only [map_add,hd0,hd1,hd2,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he3] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [map_add] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he3, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    exact ⟨a0,b0,ha0,hb0,hd',frame⟩
  have nu_af10_d3_target_nonzero (I' : AdamsComputationTheorems D' L' G)
      {a : (sequence D' .sphere).Page 3 (13,137)}
      (ha : RepresentsOnPage (sequence D' .sphere) 3 (13,137)
        (I'.interpretation.basis .sphere 13 137 0) a) : a≠0 := by
    let E := sequence D' .sphere
    have h279 : HasDifferential E 3 (8,134) (11,136)
        (I'.interpretation.basis .sphere 8 134 3) (I'.interpretation.basis .sphere 11 136 1) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
        exact List.mem_of_getElem? (i := 279) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,134) (11,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h280 : HasDifferential E 3 (8,134) (11,136)
        (I'.interpretation.basis .sphere 8 134 2) (I'.interpretation.basis .sphere 11 136 2) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
        exact List.mem_of_getElem? (i := 280) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,134) (11,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h282 : HasDifferential E 4 (11,136) (15,139)
        (I'.interpretation.basis .sphere 11 136 0) (I'.interpretation.basis .sphere 15 139 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
        exact List.mem_of_getElem? (i := 282) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 4 (11,136) (15,139) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h283 : HasDifferential E 2 (11,136) (13,137)
        (I'.interpretation.basis .sphere 11 136 4) (I'.interpretation.basis .sphere 13 137 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
        exact List.mem_of_getElem? (i := 283) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (11,136) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h281 : ReachesPage E 5 (11,136) (I'.interpretation.basis .sphere 11 136 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
        exact List.mem_of_getElem? (i := 281) (by rfl))
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 5 (11,136) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 208) (by rfl))
    change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 13 137 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 3 := he 3
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 192) (by rfl))
    change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 11 136 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 4 := hf 4
    let ell (x : E.Page 2 (13,137)) : F2 := e x 0
    have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
        (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
        RepresentsOnPage E r p (x-y) (a-b) := by
      obtain ⟨hr,z,hz,ha⟩ := hx
      obtain ⟨_,w,hw,hb⟩ := hy
      exact ⟨hr,z-w,by rw [map_sub,hz,hw],by rw [map_sub,ha,hb]⟩
    have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
        (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
      rw [←hb.eq_on_page_two] at hb
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
    have hd0 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 0)=0 := by
      obtain ⟨_,a,b,ha,_,_⟩ := h282
      exact dz (by decide) ⟨a,ha⟩
    have hd1 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 1)=0 := by
      obtain ⟨_,a,b,_,hb,_⟩ := h279
      exact dz (by decide) ⟨b,hb⟩
    have hd2 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 2)=0 := by
      obtain ⟨_,a,b,_,hb,_⟩ := h280
      exact dz (by decide) ⟨b,hb⟩
    have hd3 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 3)=0 := dz (by decide) h281
    have hd4 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 4)=I'.interpretation.basis .sphere 13 137 3 := h283.eq_on_page_two.2
    have incoming_zero (x : E.Page 2 (11,136)) : ell (E.d 2 (11,136) x)=0 := by
      have hall (a : Fin 5 →₀ F2) : ell (E.d 2 (11,136) (f.symm a))=0 := by
        dsimp only [ell]
        induction a using Finsupp.induction with
        | zero => simp
        | @single_add i c a hi hci ih =>
          rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
          fin_cases c
          · simp
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single i 1))) 0=0
            fin_cases i
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 0 1))) 0=0
              simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 1 1))) 0=0
              simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 2 1))) 0=0
              simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 3 1))) 0=0
              simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 4 1))) 0=0
              rw [hf4,hd4,←he3,LinearEquiv.apply_symm_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
    have nz3 {x : E.Page 2 (13,137)} (hx : ell x=1) {a : E.Page 3 (13,137)}
        (ha : RepresentsOnPage E 3 (13,137) x a) : a≠0 := by
      intro ha0
      obtain ⟨_,z,hz2,hz3⟩ := ha
      obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,136) z).mp (hz3.trans ha0)
      change E.d 2 (11,136) u = (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z at hu
      change (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z=x at hz2
      have hh := incoming_zero u
      rw [hu,hz2,hx] at hh
      exact one_ne_zero hh
    apply nz3 (x:=I'.interpretation.basis .sphere 13 137 0) ?_ ha
    dsimp only [ell]
    rw [←he0,LinearEquiv.apply_symm_apply]
    simp
  have boundary_of_zero_representative
      {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
      (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
      x ∈ boundaries H SphereSpectrum (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
    let P := E.ssData p
    obtain ⟨hr,z,hz,hzero⟩ := hx
    change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
    change P.pageπ ↑(r-2).toNat z=0 at hzero
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
    have hrindex : r-1-1=r-2 := by omega
    change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
    rw [hrindex]
    refine ⟨y,?_⟩
    have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
        cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
      dsimp only [boundaryMap,cycleMap,P,E]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    rw [←hf,CategoryTheory.comp_apply,hy]
    exact hz
  have nu_af10_cycles_boundary (I' : AdamsComputationTheorems D' L' G) :
      cycles H SphereSpectrum 4 (10,135) ≤ boundaries H SphereSpectrum 2 (10,135) := by
    intro x hx
    obtain ⟨a4,ha4⟩ := (isCycle_iff_represents H SphereSpectrum 5 (by decide) (10,135) x).mp
      ⟨by decide, by simpa using hx⟩
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha4
    have hd : (sequence D' .sphere).d 3 (10,135) a3=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a4,ha4⟩
    obtain ⟨a,b,ha,hb,hab,frame⟩ := nu_af10_frame I'
    have haz : a3=0 := by
      rcases frame a3 with h|h
      · exact h
      · exact (nu_af10_d3_target_nonzero I' hb (hab.symm.trans (by simpa only [h] using hd))).elim
    rw [haz] at ha3
    exact boundary_of_zero_representative (r:=3) (p:=(10,135)) ha3
  have nu_af10_cycle_quotient_zero (I' : AdamsComputationTheorems D' L' G) :
      Subsingleton (CycleQuotient H SphereSpectrum 4 2 (10,135)) := by
    have hz (x : CycleQuotient H SphereSpectrum 4 2 (10,135)) : x=0 := by
      obtain ⟨x⟩ := x
      exact (NestedQuotient.projection_eq_zero x).mpr (nu_af10_cycles_boundary I' x.property)
    exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
  have finite_sphere_zero_of_classical_quotient
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t w : ℤ)
      (hw : 0≤t-w ∧ t-w<q)
      (hc : Subsingleton (CycleQuotient H SphereSpectrum ((q:ℤ)-t+w) (1+t-w) (s,t))) :
      IsZero (((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,w)).eInfty) := by
    let e := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) w hw
    haveI := hc
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom q)).eInftyMap (s,t,w)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv q)).eInftyMap (s,t,w)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have nu_five_filtration_gap (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (a : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a := by
    apply (D'.quotientConvergence 5 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      10 11 125 134 (by decide)
    intro j hj hj'
    have : j=10 := by omega
    subst j
    exact finite_sphere_zero_of_classical_quotient BHS 5 (by decide) 10 135 134 (by norm_num)
      (nu_af10_cycle_quotient_zero I')
  have nu_three_x_gap (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (a : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a := by
    apply (D'.quotientConvergence 3 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      9 11 122 130 (by decide)
    intro j hj hj'
    have hc : Subsingleton (E2 H SphereSpectrum j (122+j)) := by
      have hjs : j=9 ∨ j=10 := by omega
      rcases hjs with rfl|rfl
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,9,131,[]⟩ (by
          exact List.mem_of_getElem? (i := 170) (by rfl))
        change E2 H SphereSpectrum 9 131 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,10,132,[]⟩ (by
          exact List.mem_of_getElem? (i := 179) (by rfl))
        change E2 H SphereSpectrum 10 132 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
    haveI := hc
    apply finite_sphere_zero_of_classical_quotient BHS 3 (by decide) j (122+j) 130
      (by constructor <;> omega)
    haveI : Subsingleton (cycles H SphereSpectrum ((3:ℤ)-(122+j)+130) (j,122+j)) := inferInstance
    refine ⟨?_⟩
    rintro ⟨x⟩ ⟨y⟩
    exact congrArg (NestedQuotient.projection _ _) (Subsingleton.elim x y)
  have sphere_quotient_high_filtration_zero (BHS : EInftyComparison D')
      (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
      (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
      (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N z) : z=0 := by
    let O : SyntheticObject := .quotient q .sphere
    have hsep : ∀ z : BiHom m w (O.obj D'.nu D'.hopfAndDetector),
        (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) j z) → z=0 :=
      D'.homotopySeparated O m w
    refine (D'.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
    intro j hj
    let i : Tridegree := (j,m+j,w)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
    have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
    haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
      dsimp only [PageRepresentatives.finiteEInftyModel]
      rw [if_neg hh]
      infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro e
    have he : (D'.family.functor.map g).eInftyMap i e=0 :=
      P.injective (Subsingleton.elim _ _)
    have h := congrArg (fun a=>(D'.family.functor.map f).eInftyMap i a) he
    change ((D'.family.functor.map g).eInftyMap i ≫ (D'.family.functor.map f).eInftyMap i) e=_ at h
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
    simpa only [ConcreteCategory.id_apply,map_zero] using h
  have nu_three_x_detection_unique (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (x : E2 H SphereSpectrum 8 130)
      (a b : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3))
      (ha : FiniteDetected D' 3 (by decide) 8 130 0 x a)
      (hb : FiniteDetected D' 3 (by decide) 8 130 0 x b) : a=b := by
    apply sub_eq_zero.mp
    apply sphere_quotient_high_filtration_zero BHS 3 (by decide) 122 130 11 (by decide)
    apply (nu_three_x_gap I' BHS (a-b)).mp
    exact detects_sub_filtration (D'.quotientConvergence 3 (by decide)) (8,130,130) ha.1 hb.1
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i = (D'.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D'.family.functor.map f).toSSDataMorphism
    let PX := (D'.family.functor.obj X).ssData i
    let PY := (D'.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D'.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D'.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat.{v} ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
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
  have detection_exists_of_infinity
      {X : Syn} (c : TowerConvergence (nuCoefficientUnit H.unit D'.nu) D'.family X)
      (i : Tridegree) (x : (D'.family.obj X).E₂ i)
      (e : ((D'.family.obj X).sequence.ssData i).eInfty)
      (hx : HasInfinityRepresentative (D'.family.obj X) 2 i x e) (hne : e≠0) :
      ∃ a : BiHom (i.2.1-i.1) i.2.2 X, DetectsNonzero c i x a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) X
    haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
      inferInstance ((c.identification i).hom e)
    exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,⟨e,hx,a,rfl,ha.symm⟩,e,hx,hne⟩
  have finite_sphere_detection_exists
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0) :
      ∃ a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) q), FiniteDetected D' q hq s t 0 x a := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-0)
      (by constructor <;> omega)
    let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
      ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
    let e := P.symm (NestedQuotient.projection _ _ y)
    have he : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-0)
        (finiteTargetLabel D' .sphere q s t 0 x) e := by
      apply (BHS.labels.1 .sphere q hq (s,t) 0 hq y e).mpr
      exact P.apply_symm_apply _
    have en : e≠0 := by
      intro hz
      have hp := congrArg P hz
      change P (P.symm _)=P 0 at hp
      rw [P.apply_symm_apply,map_zero] at hp
      have hm := (NestedQuotient.projection_eq_zero y).mp hp
      have hb : (1:ℤ)+t-(t-0)=1 := by omega
      change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
      rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
      exact hne hm
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hfg : f≫g=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.hom_inv_id,D'.quotientFunctoriality.map_id]
    let e' := (D'.family.functor.map f).eInftyMap (s,t,t-0) e
    have hel : familyPageMap D'.family f 2 (s,t,t-0) (finiteTargetLabel D' .sphere q s t 0 x)=D'.quotientLabel q s t 0 x := by
      rw [←sphere_quotient_label_to_nu q 0 s t x]
      calc
        _ = familyPageMap D'.family (g≫f) 2 (s,t,t-0) (D'.quotientLabel q s t 0 x) :=
          ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-0)) _
        _ = D'.quotientLabel q s t 0 x := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-0) ↑(2-2:ℤ).toNat) _
    have he' : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
        (D'.quotientLabel q s t 0 x) e' := by
      have hh := family_infinity_representative_map f (s,t,t-0) _ _ he
      rw [hel] at hh
      exact hh
    have en' : e'≠0 := by
      intro hz
      apply en
      have hh := congrArg (fun a=>(D'.family.functor.map g).eInftyMap (s,t,t-0) a) hz
      change ((D'.family.functor.map f).eInftyMap (s,t,t-0) ≫ (D'.family.functor.map g).eInftyMap (s,t,t-0)) e=_ at hh
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hfg,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
      simpa only [ConcreteCategory.id_apply,map_zero] using hh
    exact detection_exists_of_infinity (D'.quotientConvergence q hq) (s,t,t-0) _ e' he' en'
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
  have detection_of_filtration
      (X : SyntheticObject) (i : Tridegree)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a) :
      ∃ x : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i,
        Detects (D'.convergence X) i x a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (X.obj D'.nu D'.hopfAndDetector)
        (i.2.1-i.1,i.2.2))) (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let e := ((D'.convergence X).identification i).inv
      (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a')
    let P := (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).sequence.ssData i
    haveI : Epi (P.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (P.pageπ ⊤)).mp inferInstance e
    let x := (Subobject.ofLE _ _ (P.Z_anti le_top) ≫ P.pageπ 0) z
    refine ⟨x,e,⟨by decide,z,rfl,hz⟩,a',ha',?_⟩
    exact ConcreteCategory.congr_hom ((D'.convergence X).identification i).inv_hom_id _
  have detects_reflect
      (X Y : SyntheticObject) (f : X.obj D'.nu D'.hopfAndDetector ⟶ Y.obj D'.nu D'.hopfAndDetector)
      (i : Tridegree)
      (hi : Function.Injective (((D'.family.functor.map f).eInftyMap i).hom))
      (x : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (e : ((D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).sequence.ssData i).eInfty)
      (he : HasInfinityRepresentative (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)) 2 i x e)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a)
      (hf : DetectsNonzero (D'.convergence Y) i (familyPageMap D'.family f 2 i x) (a≫f)) :
      DetectsNonzero (D'.convergence X) i x a := by
    obtain ⟨z,hz⟩ := detection_of_filtration X i a ha
    have hm := detected_map X Y f i z a hz
    obtain ⟨ee,hz',hx'⟩ := detects_infinity_equal Y i (a≫f) _ _ hm hf.1
    obtain ⟨ez,hez,a',ha',hga⟩ := hz
    have heq : ez=e := hi ((family_infinity_representative_map f i z ez hez).unique hz' |>.trans
      (hx'.unique (family_infinity_representative_map f i x e he)))
    refine ⟨⟨e,he,a',ha',?_⟩,e,he,?_⟩
    · simpa only [heq] using hga
    · intro he0
      obtain ⟨en,hen,hn⟩ := hf.2
      have hh := hen.unique (family_infinity_representative_map f i x e he)
      exact hn (hh.trans (by rw [he0,map_zero]))
  have finite_nu_rho_injective (BHS : EInftyComparison D')
      (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
      (hw : 0≤t-w ∧ t-w < i) :
      Function.Injective (((D'.family.functor.map
        ((D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).rho i j hij)).eInftyMap (s,t,w)).hom) := by
    intro a b hab
    apply (BHS.presentation.finiteWindow SphereSpectrum j (by omega) (s,t) w
      (by constructor <;> omega)).injective
    apply PageRepresentatives.quotientMap_cycle_injective H SphereSpectrum
      (show (i:ℤ)-t+w≤(j:ℤ)-t+w by omega) (1+t-w) (s,t)
    rw [←BHS.maps.rho_finite SphereSpectrum i j hi hij (s,t) w hw a,
        ←BHS.maps.rho_finite SphereSpectrum i j hi hij (s,t) w hw b,hab]
  have finite_sphere_rho_injective (BHS : EInftyComparison D')
      (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
      (hw : 0≤t-w ∧ t-w < i) :
      Function.Injective (((D'.family.functor.map
        ((D'.quotientTower (S_0_0 : Syn)).rho i j hij)).eInftyMap (s,t,w)).hom) := by
    intro a b hab
    let gj := XModLambdaN.map D'.nu.unitIso.inv j
    let fj := XModLambdaN.map D'.nu.unitIso.hom j
    let gi := XModLambdaN.map D'.nu.unitIso.inv i
    let r := (D'.quotientTower (S_0_0 : Syn)).rho i j hij
    let r' := (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).rho i j hij
    have hcomm : r≫gi=gj≫r' := (D'.comparisonCompatible.quotient_naturality D'.nu.unitIso.inv).rho_comm hij
    have hgf : gj≫fj=𝟙 _ := by
      dsimp only [gj,fj]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq : (D'.family.functor.map gj).eInftyMap (s,t,w) a=
        (D'.family.functor.map gj).eInftyMap (s,t,w) b := by
      apply finite_nu_rho_injective BHS i j hi hij s t w hw
      have hh := congrArg (fun c=>(D'.family.functor.map gi).eInftyMap (s,t,w) c) hab
      change ((D'.family.functor.map r).eInftyMap (s,t,w)≫
        (D'.family.functor.map gi).eInftyMap (s,t,w)) a =
        ((D'.family.functor.map r).eInftyMap (s,t,w)≫
          (D'.family.functor.map gi).eInftyMap (s,t,w)) b at hh
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hcomm,
        Functor.map_comp,SpectralSequenceMorphism.eInftyMap_comp] at hh
      exact hh
    have hh := congrArg (fun c=>(D'.family.functor.map fj).eInftyMap (s,t,w) c) heq
    change ((D'.family.functor.map gj).eInftyMap (s,t,w)≫
        (D'.family.functor.map fj).eInftyMap (s,t,w)) a =
        ((D'.family.functor.map gj).eInftyMap (s,t,w)≫
          (D'.family.functor.map fj).eInftyMap (s,t,w)) b at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
    exact hh
  have finite_sphere_infinity_exists
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (k : ℕ) (hk : k<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-k) (s,t)) :
      ∃ e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty,
        HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
          (D'.quotientLabel q s t k x) e := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t) :=
      ⟨x,by rw [show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega]; exact hx⟩
    let e := P.symm (NestedQuotient.projection _ _ y)
    have he : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) e := by
      apply (BHS.labels.1 .sphere q hq (s,t) k hk y e).mpr
      exact P.apply_symm_apply _
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hfg : f≫g=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.hom_inv_id,D'.quotientFunctoriality.map_id]
    let e' := (D'.family.functor.map f).eInftyMap (s,t,t-k) e
    have hel : familyPageMap D'.family f 2 (s,t,t-k) (finiteTargetLabel D' .sphere q s t k x)=D'.quotientLabel q s t k x := by
      rw [←sphere_quotient_label_to_nu q k s t x]
      calc
        _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
        _ = D'.quotientLabel q s t k x := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have he' : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k x) e' := by
      have hh := family_infinity_representative_map f (s,t,t-k) _ _ he
      rw [hel] at hh
      exact hh
    exact ⟨e',he'⟩
  have finite_sphere_rho_label (i j k : ℕ) (hij : i≤j) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family ((D'.quotientTower (S_0_0 : Syn)).rho i j hij) 2 (s,t,t-k)
        (D'.quotientLabel j s t k x)=D'.quotientLabel i s t k x := by
    let rho := (D'.quotientTower (S_0_0 : Syn)).rho i j hij
    change familyPageMap D'.family rho 2 (s,t,t-k)
      (familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) j) 2 (s,t,t-k) (D'.sphereE2 s t k x))=_
    calc
      _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) j≫rho) 2 (s,t,t-k) (D'.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : Syn) j) rho 2 (s,t,t-k)) _
      _ = D'.quotientLabel i s t k x := by
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
        rfl
  have finite_sphere_detection_reflect (BHS : EInftyComparison D')
      (i j k : ℕ) (hi : 0 < i) (hij : i≤j) (hk : k < i) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum ((j:ℤ)-k) (s,t))
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) j))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a)
      (hf : FiniteDetected D' i hi s t k x (a≫(D'.quotientTower (S_0_0 : Syn)).rho i j hij)) :
      FiniteDetected D' j (by omega) s t k x a := by
    obtain ⟨e,he⟩ := finite_sphere_infinity_exists BHS j (by omega) k (by omega) s t x hx
    apply detects_reflect (.quotient j .sphere) (.quotient i .sphere)
      ((D'.quotientTower (S_0_0 : Syn)).rho i j hij) (s,t,t-k)
      (finite_sphere_rho_injective BHS i j hi hij s t (t-k) (by constructor <;> omega))
      (D'.quotientLabel j s t k x) e he a ha
    change DetectsNonzero (D'.quotientConvergence i hi) (s,t,t-k)
      (familyPageMap D'.family ((D'.quotientTower (S_0_0 : Syn)).rho i j hij) 2 (s,t,t-k)
        (D'.quotientLabel j s t k x)) (a≫(D'.quotientTower (S_0_0 : Syn)).rho i j hij)
    rw [finite_sphere_rho_label i j k hij s t x]
    exact hf
  have finite_sphere_infinity_nonzero
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
      (e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
      (he : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
        (D'.quotientLabel q s t 0 x) e) : e≠0 := by
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hh := family_infinity_representative_map g (s,t,t-0) _ _ he
    have hl := sphere_quotient_label_to_nu q 0 s t x
    change familyPageMap D'.family g 2 (s,t,t-0) (D'.quotientLabel q s t 0 x)=_ at hl
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
  have finite_sphere_detected_rho
      (BHS : EInftyComparison D') (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum i (s,t)) (hne : x≠0)
      (a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) j))
      (ha : FiniteDetected D' j hj s t 0 x a) :
      FiniteDetected D' i hi s t 0 x (a≫(D'.quotientTower S_0_0).rho i j hij) := by
    let rho := (D'.quotientTower S_0_0).rho i j hij
    have hl : familyPageMap D'.family rho 2 (s,t,t-0) (D'.quotientLabel j s t 0 x)=D'.quotientLabel i s t 0 x := by
      change familyPageMap D'.family rho 2 (s,t,t-0)
        (familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) j) 2 (s,t,t-0) (D'.sphereE2 s t 0 x))=_
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) j≫rho) 2 (s,t,t-0) (D'.sphereE2 s t 0 x) :=
          ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : Syn) j) rho 2 (s,t,t-0)) _
        _ = D'.quotientLabel i s t 0 x := by
          dsimp only [rho]
          rw [FiniteLambdaQuotientTower.rho_quotient]
          rfl
    have hd := detected_map (.quotient j .sphere) (.quotient i .sphere) rho (s,t,t-0) _ a ha.1
    have hd' : Detects (D'.quotientConvergence i hi) (s,t,t-0)
        (D'.quotientLabel i s t 0 x) (a≫rho) := hl ▸ hd
    refine ⟨hd',?_⟩
    obtain ⟨e,he,_⟩ := hd'
    exact ⟨e,he,finite_sphere_infinity_nonzero BHS i hi s t x hx hne e he⟩
  obtain ⟨x3,y3,hx3,hy3,heq3⟩ := hthree
  obtain ⟨xr,hxr,hxn⟩ := SF.x_to_e6
  have hX : I'.interpretation.sphere 8 130 X ∈ PageRepresentatives.cycles H SphereSpectrum 5 (8,130) :=
    ((PageRepresentatives.isCycle_iff_represents H SphereSpectrum 6 (by decide) (8,130)
      (I'.interpretation.sphere 8 130 X)).mpr ⟨xr,hxr⟩).2
  have hXn : I'.interpretation.sphere 8 130 X≠0 := by
    intro h
    rw [h] at hxr
    exact hxn (represents_unique hxr
      (RepresentsOnPage.zero (by decide : (2:ℤ)≤6)))
  obtain ⟨x5,hx5⟩ := finite_sphere_detection_exists BHS 5 (by decide) 8 130 _ hX hXn
  let rho := (D'.quotientTower (S_0_0 : Syn)).rho 3 5 (by decide)
  have hxrho : x5≫rho=x3 := by
    apply nu_three_x_detection_unique I' BHS _ _ _ _ hx3
    apply finite_sphere_detected_rho BHS 3 5 (by decide) (by decide) (by decide) 8 130 _ _ hXn x5 hx5
    exact PageRepresentatives.cycles_antitone H SphereSpectrum (8,130) (by decide : (3:ℤ)≤5) hX
  have hlam : lambdaMultiply 0 nu=nu := by
    have hc := D'.shiftCoherence.right_unit (3,4) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 3 4 : Syn) := by
      change (biShiftAddIso (3,4) (0,0) (3,4) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (3,4) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn) ≫ nu=nu
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hnud := D'.comparisonCompatible.homotopy_lambda 1 4 0 nu
  rw [hnu,hlam] at hnud
  have hp : Sphere.Internal.product H M' (s:=1) (t:=4) (s':=8) (t':=130)
      (Sphere.Internal.hi H M' 2) (I'.interpretation.sphere 8 130 X)=0 := by
    have hp := I'.products ⟨1,4,8,130⟩ (by
      exact List.mem_of_getElem? (i := 46) (by rfl)) (atom .h2) X
    dsimp only at hp
    rw [I'.distinguishedClasses.h2] at hp
    rw [←hp]
    have hmul : mulAt (atom .h2) X=mulAt X (atom .h2) := by
      apply Subtype.ext
      exact mul_comm _ _
    rw [hmul]
    exact SF.x_h2_zero
  have hy10 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10
      (show BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5) from sphereAction nu x5) := by
    have hd := compatibility.finite_action 5 (by decide) 1 4 8 130 0 0
      (Sphere.Internal.hi H M' 2) (I'.interpretation.sphere 8 130 X) nu x5 hnud hx5.1
    change Detects (D'.quotientConvergence 5 (by decide)) (9,134,134)
      (D'.quotientLabel 5 9 134 0
        (Sphere.Internal.product H M' (s:=1) (t:=4) (s':=8) (t':=130)
          (Sphere.Internal.hi H M' 2) (I'.interpretation.sphere 8 130 X))) (sphereAction nu x5) at hd
    rw [hp] at hd
    have hz : D'.quotientLabel 5 9 134 0 (0 : E2 H SphereSpectrum 9 134)=0 := by
      simp only [AdamsComparisonData.quotientLabel,map_zero]
    rw [hz] at hd
    exact detects_zero_filtration (D'.quotientConvergence 5 (by decide)) (9,134,134) hd
  have hy11 := (nu_five_filtration_gap I' BHS (sphereAction nu x5)).mp hy10
  refine ⟨x5,sphereAction nu x5,hx5,?_,rfl⟩
  refine finite_sphere_detection_reflect BHS 3 5 2 (by decide) (by decide) (by decide) 11 136
    (I'.interpretation.sphere 11 136 Y) ?_ (sphereAction nu x5) hy11 ?_
  · obtain ⟨yr,hyr,_⟩ := SF.y_to_e5
    have hc := ((PageRepresentatives.isCycle_iff_represents H SphereSpectrum 5 (by decide)
      (11,136) (I'.interpretation.sphere 11 136 Y)).mpr ⟨yr,hyr⟩).2
    exact PageRepresentatives.cycles_antitone H SphereSpectrum (11,136) (by decide : (3:ℤ)≤4) hc
  · have heq : sphereAction nu x5≫rho=y3 := by
      calc
        _ = sphereAction nu (x5≫rho) := by simp only [sphereAction,Category.assoc]
        _ = y3 := by rw [hxrho,heq3]
    change FiniteDetected D' 3 (by decide) 11 136 2 (I'.interpretation.sphere 11 136 Y)
      (sphereAction nu x5≫rho)
    rw [heq]
    exact hy3

end
end NuFiveFromThreeProof


/-- The actual Q3 Hopf relation, extracted before the Q3-to-Q5 lifting step.
Both detected classes and the equation use the same model and quotient. -/
theorem nu_extension_in_third_quotient : NuExtension3 D eX eY h2 := by
  let SF := KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing
  obtain ⟨huq,κ,hκ,x,y,hxn,hx,hy,hxy⟩ := nu_three_actual_relation_and_unique
    literatureTheorems.synthetic.eInfty literatureTheorems.may.toMayContext I
    literatureTheorems.applicability.nuCofiber
    (KIP126.Main.ExtensionLaws.generalizedMahowald_minimal_middle D literatureTheorems.synthetic literatureTheorems.may
      (D).hopfAndDetector.nuCofiberTriangle 0
      (by rw [literatureTheorems.applicability.nuCofiber.bottom_exponent]; rfl))
    (KIP126.Computation.SphereAndCofiber.cnu_d3 I) SF
  refine ⟨x,y,hx,hy,?_⟩
  rw [q3_sphere_action_actual_map D literatureTheorems.synthetic.eInfty literature.sources.sourceComparisons.algebra
    literature.sources.sourceComparisons.quotientCompatibility literatureTheorems.may.toMayContext huq κ hκ h2 x hxn]
  exact hxy

/-- `lem:nuext125`, the substantial Q3-to-Q5 step: all AF10 correction
classes must be checked in the full E2(10,135) space, including linear
combinations, with BHS lifetime and the actual rho map. The conclusion is
an exact existential lifting relation, not the false assertion that this
five-dimensional E2 group vanishes or that all representatives vanish. -/
theorem nu_extension_lifts_to_fifth_quotient : NuExtension5 D eX eY h2 := by
  let SF := KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing
  exact nu_five_of_three I literatureTheorems.synthetic.eInfty literature.sources.sourceComparisons.algebra
    literature.sources.sourceComparisons.algebraDetectionCompatibility SF h2 literatureTheorems.applicability.nuCofiber.normalized_label
    nu_extension_in_third_quotient

end
end KIP126.Main.SectionSeven
