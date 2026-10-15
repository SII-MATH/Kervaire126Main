module

public import KIP126.Main.SectionSeven.TodaDetection

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

section ConditionalYDetection
open CategoryTheory.Limits KIP126.Algebra
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD

private theorem finite_detected_y_d5_zero
    (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 11 136)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hz : FiniteDetected D' 9 (by decide) 11 136 4 x z) :
    KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 5 (11,136) (16,140) x 0 := by
  classical

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

  have quotient_nu_detection_cycles
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 11 136)
      (e : ((D'.family.nuQuotient D'.nu SphereSpectrum 9).sequence.ssData (11,136,132)).eInfty)
      (hx : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 9) 2 (11,136,132)
        (finiteTargetLabel D' .sphere 9 11 136 4 x) e) :
      x ∈ PageRepresentatives.cycles H SphereSpectrum 5 (11,136) := by
    let P := BHS.presentation
    let Z5 := PageRepresentatives.cycles H SphereSpectrum 5 (11,136)
    let Z1 := PageRepresentatives.cycles H SphereSpectrum 1 (11,136)
    let B5 := PageRepresentatives.boundaries H SphereSpectrum 5 (11,136)
    have hsurj : Function.Surjective (NestedQuotient.projection Z5 B5) := by rintro ⟨a⟩; exact ⟨a,rfl⟩
    obtain ⟨x',hx'⟩ := hsurj (P.finiteWindow SphereSpectrum 9 (by decide) (11,136) 132 (by decide) e)
    have hrep' : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 9) 2 (11,136,132)
        (finiteTargetLabel D' .sphere 9 11 136 4 x'.val) e :=
      (BHS.labels.1 .sphere 9 (by decide) (11,136) 4 (by decide) x' e).mpr hx'.symm
    let rho := (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).rho 5 9 (by decide)
    let e5 := ((D'.family.functor.map rho).eInftyMap (11,136,132)) e
    have restrict (y : E2 H SphereSpectrum 11 136)
        (hy : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 9) 2 (11,136,132)
          (finiteTargetLabel D' .sphere 9 11 136 4 y) e) :
        HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 5) 2 (11,136,132)
          (finiteTargetLabel D' .sphere 5 11 136 4 y) e5 := by
      have hh := family_infinity_representative_map rho (11,136,132) _ _ hy
      have hlabel : familyPageMap D'.family rho 2 (11,136,132) (finiteTargetLabel D' .sphere 9 11 136 4 y)=
          finiteTargetLabel D' .sphere 5 11 136 4 y := by
        change familyPageMap D'.family rho 2 (11,136,132)
          (familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 9) 2 (11,136,132)
            (targetNuLabel D' .sphere 11 136 4 y)) =
          familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 5) 2 (11,136,132)
            (targetNuLabel D' .sphere 11 136 4 y)
        rw [←CategoryTheory.comp_apply,family_page_comp]
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
      exact hlabel ▸ hh
    let y : Z1 := ⟨x,by dsimp only [Z1]; rw [PageRepresentatives.cycles_one]; trivial⟩
    let y' : Z1 := ⟨x'.val,by dsimp only [Z1]; rw [PageRepresentatives.cycles_one]; trivial⟩
    have hy := (BHS.labels.1 .sphere 5 (by decide) (11,136) 4 (by decide) y e5).mp (restrict x hx)
    have hy' := (BHS.labels.1 .sphere 5 (by decide) (11,136) 4 (by decide) y' e5).mp (restrict x'.val hrep')
    have heq : NestedQuotient.projection Z1 B5 y=NestedQuotient.projection Z1 B5 y' := hy.symm.trans hy'
    have hd : x-x'.val ∈ B5 := by
      apply (NestedQuotient.projection_eq_zero (y-y')).mp
      rw [map_sub,heq,sub_self]
    have hz : x-x'.val ∈ Z5 := PageRepresentatives.boundaries_le_cycles H SphereSpectrum (11,136) 5 5 hd
    have hh := Z5.add_mem hz x'.property
    simpa only [sub_add_cancel] using hh

  have finite_sphere_detection_cycles
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 11 136)
      (z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
      (hz : FiniteDetected D' 9 (by decide) 11 136 4 x z) :
      x ∈ PageRepresentatives.cycles H SphereSpectrum 5 (11,136) := by
    obtain ⟨_,e,he,hen⟩ := hz
    let f := XModLambdaN.map D'.nu.unitIso.inv 9
    have hbase : familyPageMap D'.family D'.nu.unitIso.inv 2 (11,136,132) (D'.sphereE2 11 136 4 x)=
        targetNuLabel D' .sphere 11 136 4 x := by
      have hc := D'.comparisonCompatible.sphere_nu 11 136 4 x
      calc
        _ = familyPageMap D'.family D'.nu.unitIso.inv 2 (11,136,132)
            (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (11,136,132)
              (D'.nuE2 .sphere 0 11 136 4 x)) := congrArg (fun y => familyPageMap D'.family D'.nu.unitIso.inv 2 (11,136,132) y) hc.symm
        _ = familyPageMap D'.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) ≫ D'.nu.unitIso.inv)
            2 (11,136,132) (D'.nuE2 .sphere 0 11 136 4 x) :=
          ConcreteCategory.congr_hom (family_page_comp  (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (11,136,132)) (D'.nuE2 .sphere 0 11 136 4 x)
        _ = targetNuLabel D' .sphere 11 136 4 x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          rfl
    have hlabel : familyPageMap D'.family f 2 (11,136,132) (D'.quotientLabel 9 11 136 4 x)=
        finiteTargetLabel D' .sphere 9 11 136 4 x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) 9 ≫ XModLambdaN.map D'.nu.unitIso.inv 9)
            2 (11,136,132) (D'.sphereE2 11 136 4 x) :=
          ConcreteCategory.congr_hom (family_page_comp  (XModLambdaN.incl (S_0_0 : Syn) 9) (XModLambdaN.map D'.nu.unitIso.inv 9) 2 (11,136,132)) (D'.sphereE2 11 136 4 x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 9)
            2 (11,136,132) (D'.sphereE2 11 136 4 x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 9) 2 (11,136,132)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (11,136,132) (D'.sphereE2 11 136 4 x)) :=
          (ConcreteCategory.congr_hom (family_page_comp  D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 9) 2 (11,136,132)) (D'.sphereE2 11 136 4 x)).symm
        _ = finiteTargetLabel D' .sphere 9 11 136 4 x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) 9) 2 (11,136,132) y) hbase
    have hh := family_infinity_representative_map f (11,136,132) _ _ he
    rw [hlabel] at hh
    exact quotient_nu_detection_cycles BHS x _ hh

  have represents_unique
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
    obtain ⟨hr, z, hz, hza⟩ := ha
    obtain ⟨_, z', hz', hzb⟩ := hb
    let D' := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    have hnm : n ≤ m := by
      dsimp only [n, m]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
    apply sub_eq_zero.mp
    rw [← hza, ← hzb, ← map_sub]
    apply (subobject_cokernel_π_eq_zero_iff (D'.B m) (D'.Z m) (D'.B_le_Z m) _).mpr
    have heq : D'.pageπ n ((Subobject.ofLE _ _ (D'.Z_anti hnm)) (z-z')) = 0 := by
      change (Subobject.ofLE _ _ (D'.Z_anti hnm) ≫ D'.pageπ n) (z-z') = 0
      rw [map_sub, hz, hz', sub_self]
    have hh := (subobject_cokernel_π_eq_zero_iff (D'.B n) (D'.Z n) (D'.B_le_Z n) _).mp heq
    have he : (D'.Z n).arrow ((Subobject.ofLE _ _ (D'.Z_anti hnm)) (z-z')) =
        (D'.Z m).arrow (z-z') := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D'.Z_anti hnm)) _
    rw [he] at hh
    exact (ModuleCat.subobjectModule D'.V).monotone (D'.B_mono hnm) hh

  have represents_d_zero_of_later
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : RepresentsOnPage E r p x a)
      (ht : ReachesPage E t p x) : E.d r p a = 0 := by
    obtain ⟨b, ht2, z, hz, _⟩ := ht
    let D' := E.ssData p
    let nt : WithTop ℕ := ↑(t-E.r₀).toNat
    let nr : WithTop ℕ := ↑(r-E.r₀).toNat
    let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
    have hrs : nr ≤ ns := by
      dsimp only [nr, ns]
      exact_mod_cast (show (r-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
    have hst : ns ≤ nt := by
      dsimp only [ns, nt]
      exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
    let zr := (Subobject.ofLE (D'.Z nt) (D'.Z nr) (D'.Z_anti (hrs.trans hst))) z
    have hrep : RepresentsOnPage E r p x (D'.pageπ nr zr) := by
      refine ⟨ha.1, zr, ?_, rfl⟩
      dsimp only [zr]
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      exact hz
    rw [represents_unique ha hrep]
    change D'.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
    rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
    refine ⟨(Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z, ?_⟩
    change (Subobject.ofLE (D'.Z ns) (D'.Z nr) (D'.Z_anti hrs) ≫ D'.pageπ nr)
      ((Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z) = D'.pageπ nr zr
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl

  have represents_before
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
      {x : E.Page 2 p} {xt : E.Page t p}
      (hr : 2 ≤ r) (hrt : r ≤ t) (ht : RepresentsOnPage E t p x xt) :
      ∃ xr, RepresentsOnPage E r p x xr := by
    obtain ⟨_, z, hz, _⟩ := ht
    let D' := E.ssData p
    have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(t-E.r₀).toNat := by
      exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
    let zr := (Subobject.ofLE (D'.Z ↑(t-E.r₀).toNat) (D'.Z ↑(r-E.r₀).toNat) (D'.Z_anti hrt')) z
    refine ⟨D'.pageπ _ zr, hr, zr, ?_, rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  have hx5 := finite_sphere_detection_cycles BHS x z hz
  obtain ⟨x6,hx6⟩ := (PageRepresentatives.isCycle_iff_represents H SphereSpectrum 6 (by decide) (11,136) x).mp ⟨by decide,hx5⟩
  obtain ⟨x5,hx5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) hx6
  have hd : E.d 5 (11,136) x5=0 := represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6) hx5 ⟨x6,hx6⟩
  exact ⟨rfl,x5,0,hx5,KIP126.SpectralSequence.RepresentsOnPage.zero (by decide),hd⟩
end ConditionalYDetection

/-- Remark 7.17 (`rem:h02x1259`): only under both paper conditions can the
newly constructed Q9 detection rule out the previously unknown d5(Y).
The page representative is part of HasDifferential. -/
theorem conditional_y_d5_zero
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M (D).toAdamsComparisonData L η) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      5 (11,136) (16,140) eY 0 := by
  obtain ⟨a11,ha⟩ := lemma_7_14_alpha_one_exists
  obtain ⟨⟨z,hz⟩,hdet⟩ := lemma_7_16_toda_bracket_detected hc3 hc5 a11 ha
  exact finite_detected_y_d5_zero literatureTheorems.synthetic.eInfty eY z (hdet z hz)


end
end KIP126.Main.SectionSeven
