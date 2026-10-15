module

public import KIP126.Main.Computation.SphereAndCofiber.Consequences
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.QuotientTower.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs

@[expose] public section
namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2 KIP126.Algebra PageRepresentatives
open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

private theorem family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
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
private theorem family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
private theorem family_infinity_representative_map
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
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


private theorem sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x) = finiteTargetLabel D .sphere q s t k x := by
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
        ConcreteCategory.congr_hom (family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel

private theorem sphere_finite_detection_nonzero
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
    (hn : x∉boundaries H SphereSpectrum (1+t-(t-k)) (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
    (ha : Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x) a) :
    DetectsNonzero (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x) a := by
  refine ⟨ha,?_⟩
  obtain ⟨e,he,aa,haa,hgr⟩ := ha
  refine ⟨e,he,?_⟩
  intro he0
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have henu := family_infinity_representative_map (D:=D) g (s,t,t-k) _ _ he
  change HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
    (familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x)) ((D.family.functor.map g).eInftyMap (s,t,t-k) e) at henu
  rw [sphere_quotient_label_to_nu (D:=D) q k s t x,he0,map_zero] at henu
  have hh := (BHS.labels.1 .sphere q hq (s,t) k hk ⟨x,hx⟩ 0).mp henu
  rw [map_zero] at hh
  exact hn ((NestedQuotient.projection_eq_zero ⟨x,hx⟩).mp hh.symm)

private theorem survives_twelve_not_boundary_eleven (X : C) (p : ℤ × ℤ)
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


namespace MainTodaCycles
variable {R:Type u} [Ring R] {E:KIP126.SpectralSequence (ModuleCat.{v} R) (ℤ×ℤ)}
  {r:ℤ} {p q:ℤ×ℤ} {x:E.Page 2 p} {y:E.Page 2 q}
private theorem choice_represents_unique {a b : E.Page r p}
    (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
  obtain ⟨hr, z, hz, hza⟩ := ha
  obtain ⟨_, z', hz', hzb⟩ := hb
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(r - E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n, m]
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
  apply sub_eq_zero.mp
  rw [← hza, ← hzb, ← map_sub]
  apply (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) _).mpr
  have heq : D.pageπ n ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) = 0 := by
    change (Subobject.ofLE _ _ (D.Z_anti hnm) ≫ D.pageπ n) (z-z') = 0
    rw [map_sub, hz, hz', sub_self]
  have hh := (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mp heq
  have he : (D.Z n).arrow ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) =
      (D.Z m).arrow (z-z') := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti hnm)) _
  rw [he] at hh
  exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hh

private theorem choice_next_projection_zero_iff_incoming
    (E : KIP126.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat R)) :
    (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
      (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
        LinearMap.range (E.d r p).hom := by
  let D := E.ssData (p+E.diffDeg r)
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let j := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
    ((D.B_le_Z _).trans (D.Z_anti hnm))
  rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
  change D.pageπ ↑(n+1) z = 0 ↔ (i ≫ D.pageπ ↑n) z ∈ LinearMap.range (j ≫ D.pageπ ↑n).hom
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) z).mp hz
    refine ⟨v, ?_⟩
    rw [← hv]
    change (j ≫ D.pageπ ↑n) v =
      ((Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) ≫ i ≫ D.pageπ ↑n) v
    congr 2
    dsimp only [i,j]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  · rintro ⟨v, hv⟩
    apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) z).mpr
    have hz : D.pageπ ↑n (i z-j v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
    have hb' := (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
    have hv' : (D.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D.V) (D.B ↑(n+1)) := by
      change (j ≫ (D.Z ↑n).arrow) v ∈ _
      dsimp only [j]
      rw [Subobject.ofLE_arrow]
      exact ⟨v, rfl⟩
    have hh := ((ModuleCat.subobjectModule D.V) (D.B ↑(n+1))).add_mem hb' hv'
    rw [map_sub, sub_add_cancel] at hh
    change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hh
    dsimp only [i] at hh
    rwa [Subobject.ofLE_arrow] at hh

private theorem choice_next_nonzero_of_not_hit
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) (hnot : ¬ HitOnPage E r p x) : a ≠ 0 := by
  generalize hq : p-E.diffDeg r=q
  have hp : p=q+E.diffDeg r := by rw [←hq]; abel
  subst p
  obtain ⟨_,z,hz,hza⟩ := ha
  let A := E.ssData (q+E.diffDeg r)
  have hi : (r+1-E.r₀).toNat=(r-E.r₀).toNat+1 := by omega
  have hnm : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(r+1-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  let br := (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) z
  have hbr : RepresentsOnPage E r (q+E.diffDeg r) x br := by
    refine ⟨hr, (Subobject.ofLE _ _ (A.Z_anti hnm)) z, ?_, rfl⟩
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have heb : br=b := choice_represents_unique hbr hb
  intro ha0
  have hv := choice_next_projection_zero_iff_incoming E r hr0 q
  have hv' : ∀ zz : (Subobject.underlying.obj (A.Z ↑(r+1-E.r₀).toNat) : ModuleCat R),
      A.pageπ ↑(r+1-E.r₀).toNat zz=0 ↔
        (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
          LinearMap.range (E.d r q).hom := by
    have transport (m : ℕ) (hm : m=(r-E.r₀).toNat+1)
        (hge : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑m) :
        ∀ zz : (Subobject.underlying.obj (A.Z ↑m) : ModuleCat R),
          A.pageπ ↑m zz=0 ↔
            (Subobject.ofLE _ _ (A.Z_anti hge) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
              LinearMap.range (E.d r q).hom := by
      subst m
      exact hv
    exact transport _ hi hnm
  have hmem : br∈LinearMap.range (E.d r q).hom := by
    exact (hv' z).mp (hza.trans ha0)
  obtain ⟨c,hc⟩ := hmem
  apply hnot
  refine ⟨q, rfl, c,b,hb,hne,?_⟩
  simpa only [eqToHom_refl, Category.comp_id] using hc.trans heb

private theorem choice_permanent_survives_of_no_early_hit
    (hstart : E.r₀≤2) (N : ℕ) (hN : 2≤N)
    (hperm : IsPermanentCycle E p x) (hne : x≠0)
    (hnot : ∀ r : ℤ, 2≤r → r<N → ¬HitOnPage E r p x) :
    SurvivesTo E N p x := by
  obtain ⟨z,hz⟩ := hperm
  let A := E.ssData p
  have hrep (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hall (n : ℕ) : n+2≤N → SurvivesTo E ((n:ℤ)+2) p x := by
    induction n with
    | zero =>
      intro hn
      obtain ⟨a,ha⟩ := hrep 2 (by omega)
      change SurvivesTo E 2 p x
      exact ⟨a,ha,by rw [←ha.eq_on_page_two]; exact hne⟩
    | succ n ih =>
      intro hn
      obtain ⟨b,hb,hbn⟩ := ih (by omega)
      obtain ⟨a,ha⟩ := hrep ((n:ℤ)+2+1) (by omega)
      have han := choice_next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h

private theorem choice_nonzero_differential_not_zero
    (h : HasNonzeroDifferential E r p q x y)
    (hzero : HasDifferential E r p q x 0) : False := by
  obtain ⟨he,a,b,ha,hb,hd,hbn⟩ := h
  obtain ⟨he',a',b',ha',hb',hd'⟩ := hzero
  have haa : a=a' := choice_represents_unique ha ha'
  have hbb : b'=0 := choice_represents_unique hb' (RepresentsOnPage.zero hb'.1)
  apply hbn
  calc b = (E.d r p ≫ eqToHom (congrArg (E.Page r) he)) a := hd.symm
       _ = b' := by simpa only [haa] using hd'
       _ = 0 := hbb

end MainTodaCycles
open KIP126.Computation.SphereAndCofiber MainTodaCycles
variable {L:SphereAdamsClasses H} {G:TmfDetectionClasses H}
open KIP126.Computation.Near126
private theorem sphere_class_identifications (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 8 134 W = L.W ∧
    I.interpretation.sphere 10 134 U = L.U M ∧
    I.interpretation.sphere 14 139 T = L.target M := by
  have hU := I.products ⟨2, 2, 8, 132⟩ (by simp [Raw.products]) h0Sq (atom .x_124_8)
  have h14 := I.products ⟨1, 2, 1, 16⟩ (by simp [Raw.products]) dataH1 (atom .h4)
  have hT := I.products ⟨2, 18, 12, 121⟩ (by simp [Raw.products])
    (mulAt dataH1 (atom .h4)) (atom .x_109_12)
  dsimp only at hU h14 hT
  have hAssoc : T = mulAt (mulAt dataH1 (atom .h4)) (atom .x_109_12) := by
    apply Subtype.ext
    exact (mul_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · change I.interpretation.sphere 8 134
      (atom .x_126_8_4 + atom .x_126_8) = L.x_126_8_4 + L.x_126_8
    rw [map_add, I.distinguishedClasses.x_126_8_4, I.distinguishedClasses.x_126_8]
  · simpa only [U, SphereAdamsClasses.U, I.distinguishedClasses.h0_square, I.distinguishedClasses.x_124_8] using hU
  · rw [hAssoc, hT, h14, I.distinguishedClasses.h1, I.distinguishedClasses.h4, I.distinguishedClasses.x_109_12]
    rfl

private theorem target_survives_twelve_of_d6_vanishes
    (I:AdamsComputationTheorems D L G) (SF:Derived.SphereFacts I.interpretation) (hc3:Stem126D6Vanishes L) :
    SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) := by
  have labels:=sphere_class_identifications I
  have hp:=SF.t_permanent_cycle
  rw [labels.2.2] at hp
  have hn:L.target M≠0 := by
    intro hz
    apply SF.t_not_h0_multiple
    refine ⟨0,?_⟩
    rw [labels.2.2,hz]
    simp only [Sphere.Internal.product,map_zero]
  apply choice_permanent_survives_of_no_early_hit (by change (2:ℤ)≤2; decide) 12 (by decide) hp hn
  intro r hr hr12 hit
  rw [←labels.2.2] at hit
  rcases SF.t_only_incoming r hit with ⟨he,hd⟩|⟨he,_⟩
  · subst r
    change HasNonzeroDifferential (sequence D .sphere) 6 (8,134) (14,139)
      (I.interpretation.sphere 8 134 KIP126.Computation.Near126.W)
      (I.interpretation.sphere 14 139 KIP126.Computation.Near126.T) at hd
    rw [labels.1,labels.2.2] at hd
    exact choice_nonzero_differential_not_zero hd hc3
  · omega


private def shiftSwap (a b : ℤ × ℤ) (A : Syn) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
    (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
  (biShiftAddIso a b (a+b) rfl).app A ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm

omit [HasFunctorialCofiber (C := Syn)] in
private theorem shiftSwap_add (coh : BiShiftCoherence Syn)
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


omit [HasFunctorialCofiber (C := Syn)] in
private theorem shiftSwap_add_eq (coh : BiShiftCoherence Syn)
    (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
    (shiftSwap a d A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
    (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
      (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  subst d
  exact shiftSwap_add coh a b c A

omit [HasFunctorialCofiber (C := Syn)] in
private theorem shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
    (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
      (shiftSwap a b B).hom =
    (shiftSwap a b A).hom ≫
      (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
  exact ((biShiftAddIso a b (a+b) rfl) ≪≫
    (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f

omit [HasFunctorialCofiber (C := Syn)] in
private theorem shiftSwap_hom_eq (a b d : ℤ × ℤ)
    (hab : a+b=d) (hba : b+a=d) (A : Syn) :
    (shiftSwap a b A).hom =
      (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
  subst d
  rfl

omit [HasFunctorialCofiber (C := Syn)] in
private theorem lambda_pow_shift (coh : BiShiftCoherence Syn)
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



omit [HasFunctorialCofiber (C := Syn)] in
private theorem shift_assoc_inv (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi
private theorem lambda_left_eight (D : AdamsComparison H M Syn)
    (etaShuffle : BiHom 0 0 (S_0_0 : Syn))
    {A : Syn} (a : BiHom 125 139 A) :
    sphereAction (lambdaMultiply 8 etaShuffle) a = lambdaMultiply 8 (sphereAction etaShuffle a) := by
  let S := (S_0_0 : Syn)
  have h₁ := shift_assoc_inv D.shiftCoherence (0,0) (125,139) (0,-8)
    (125,139) (125,131) (125,131) (by decide) (by decide) (by decide) (by decide) S
  have h₂ := shift_assoc_inv D.shiftCoherence (0,0) (0,-8) (125,139)
    (0,-8) (125,131) (125,131) (by decide) (by decide) (by decide) (by decide) S
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at h₁ h₂
  have hp :
    (SyntheticCategory.biShift_comp (125,139) (0,-8)).inv.app S ≫
      lambdaPow 8 (Smn 125 139) ≫
      (SyntheticCategory.biShift_comp (0,0) (125,139)).inv.app S =
    (SyntheticCategory.biShift_comp (0,-8) (125,139)).inv.app S ≫
      (SyntheticCategory.biShift (125,139)).map
        ((SyntheticCategory.biShift_comp (0,0) (0,-8)).inv.app S) ≫
      (SyntheticCategory.biShift (125,139)).map (lambdaPow 8 (Smn 0 0)) := by
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift_comp (125,139) (0,-8)).inv.app S ≫
      (SyntheticCategory.biShift (0,-8)).map ((SyntheticCategory.biShift_comp (0,0) (125,139)).inv.app S) ≫
      lambdaPow 8 ((SyntheticCategory.biShift (125,139)).obj (Smn 0 0)) = _
    rw [lambda_pow_shift D.shiftCoherence 8 (125,139) (Smn 0 0)]
    dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
    simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
      Category.comp_id,Category.id_comp]
    simp only [Category.assoc]
    erw [←Category.assoc ((SyntheticCategory.biShift_comp (125,139) (0,-8)).inv.app S)]
    erw [h₁]
    simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (125,139)).map (lambdaPow 8 (Smn 0 0))) h₂.symm)
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
  simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
    (congrArg (fun z => z ≫ (SyntheticCategory.biShift (125,139)).map etaShuffle ≫ a) hp).symm

private def sphere_unit (_D : AdamsComparison H M Syn) : BiHom 0 0 (S_0_0 : Syn) :=
  SyntheticCategory.biShift_zero.hom.app _
private def sphere_unit_label (D : AdamsComparison H M Syn) : E2 H SphereSpectrum 0 0 :=
  D.sphereFirstQuotient 0 0 (quotientClass 1 (sphere_unit D))


private theorem sphere_unit_action_139 (D : AdamsComparison H M Syn) {A : Syn}
    (a : BiHom 125 139 A) : sphereAction (sphere_unit D) a = a := by
  have hu := D.shiftCoherence.left_unit (125,139) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  unfold sphereAction sphere_unit
  erw [←hu,Iso.inv_hom_id_app_assoc]

private theorem sphere_unit_label_product_139
    (A : AdamsAlgebraStructures D) (qb : QuotientAlgebraCompatibility D A) (ab : AlgebraDetectionCompatibility D A)
    (y : E2 H SphereSpectrum 14 139) :
    Sphere.Internal.product H M (s:=0) (t:=0) (s':=14) (t':=139) (sphere_unit_label D) y = y := by
  letI := A.syntheticSymmetric
  let b := (D.sphereFirstQuotient 14 139).symm y
  have hb : D.sphereFirstQuotient 14 139 b = y := (D.sphereFirstQuotient 14 139).apply_symm_apply y
  have h := ab.first_quotient 0 0 14 139 (quotientClass 1 (sphere_unit D)) b
  change D.sphereFirstQuotient 14 139
    (KIP126.Literature.AdamsSynthetic.algebraProduct (A.quotients.algebra 1 (by decide))
      (quotientClass 1 (sphere_unit D)) b) = _ at h
  rw [qb.sphere_action 1 (by decide) 0 0 125 139,sphere_unit_action_139] at h
  change D.sphereFirstQuotient 14 139 b =
    Sphere.Internal.product H M (s:=0) (t:=0) (s':=14) (t':=139) (sphere_unit_label D)
      (D.sphereFirstQuotient 14 139 b) at h
  rw [hb] at h
  exact h.symm


private theorem lambda_eight_target_detected
    (A : AdamsAlgebraStructures D) (qb : QuotientAlgebraCompatibility D A) (ab : AlgebraDetectionCompatibility D A)
    (y : E2 H SphereSpectrum 14 139)
    (a : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9))
    (ha : Detects (D.quotientConvergence 9 (by decide)) (14,139,139)
      (D.quotientLabel 9 14 139 0 y) a) :
    Detects (D.quotientConvergence 9 (by decide)) (14,139,131)
      (D.quotientLabel 9 14 139 8 y) (lambdaMultiply 8 a) := by
  have hu := D.comparisonCompatible.homotopy_lambda 0 0 8 (sphere_unit D)
  have hh := ab.finite_action 9 (by decide) 0 0 14 139 8 0
    (sphere_unit_label D) y (lambdaMultiply 8 (sphere_unit D)) a hu ha
  change Detects (D.quotientConvergence 9 (by decide)) (14,139,131)
    (D.quotientLabel 9 14 139 8
      (Sphere.Internal.product H M (s:=0) (t:=0) (s':=14) (t':=139) (sphere_unit_label D) y))
    (sphereAction (lambdaMultiply 8 (sphere_unit D)) a) at hh
  rw [sphere_unit_label_product_139 A qb ab y, lambda_left_eight D, sphere_unit_action_139 D] at hh
  exact hh

private theorem nonzero_detection_ne_zero
    {HS : Syn} {unit : S_0_0 ⟶ HS} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree) (x : (F.obj X).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 X) (ha : DetectsNonzero c i x a) : a≠0 := by
  intro hz
  obtain ⟨⟨e,he,b,hb,hgr⟩,e',he',hne⟩ := ha
  have hbb : b=0 := by
    apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono
      ((towerFiltration unit X).F i.1 (i.2.1-i.1,i.2.2)).arrow)
    simpa only [map_zero,hz] using hb
  have hez : e=0 := by
    apply (ModuleCat.mono_iff_injective (c.identification i).hom).mp inferInstance
    simpa only [hbb,map_zero] using hgr
  exact hne ((he'.unique he).trans hez)

private theorem nu_target_lambda_eight_nonzero
    (I : AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation) (BHS : EInftyComparison D)
    (A : AdamsAlgebraStructures D) (qb : QuotientAlgebraCompatibility D A) (ab : AlgebraDetectionCompatibility D A)
    (hc3 : Stem126D6Vanishes L) (t : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9))
    (ht : FiniteDetected D 9 (by decide) 14 139 0 (L.target M) t) :
    lambdaMultiply 8 t ≠ 0 := by
  have hd := lambda_eight_target_detected A qb ab (L.target M) t ht.1
  have hp := SF.t_permanent_cycle
  rw [(sphere_class_identifications I).2.2] at hp
  have hn := sphere_finite_detection_nonzero BHS 9 8 (by decide) (by decide) 14 139
    (L.target M) (permanentCycles_le_cycles H SphereSpectrum (14,139) _ hp) (by
      intro hb
      exact survives_twelve_not_boundary_eleven SphereSpectrum (14,139) (L.target M)
        (target_survives_twelve_of_d6_vanishes I SF hc3)
        (boundaries_monotone H SphereSpectrum (14,139) (by decide) hb)) _ hd
  exact nonzero_detection_ne_zero (D.quotientConvergence 9 (by decide)) (14,139,131) _ _ hn

private theorem lambda_two_six_139 (D : AdamsComparison H M Syn)
    {X : Syn} (c : BiHom 125 139 X) :
    lambdaMultiply 2 (lambdaMultiply 6 c) = lambdaMultiply 8 c := by
  have ha := shift_assoc_inv D.shiftCoherence (125,139) (0,-6) (0,-2)
    (125,133) (0,-8) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (125,139) (0,-6)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 2 (lambdaPow 6 (Smn 125 139)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 6 2 8 (by decide) (Smn 125 139)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl

private theorem toda_representative_lambda_two_h0_nonzero
    (I : AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation) (BHS : EInftyComparison D)
    (A : AdamsAlgebraStructures D) (qb : QuotientAlgebraCompatibility D A) (ab : AlgebraDetectionCompatibility D A)
    (hc3 : Stem126D6Vanishes L) (h0 : BiHom 0 1 (S_0_0 : Syn))
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (t : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9))
    (ht : FiniteDetected D 9 (by decide) 14 139 0 (L.target M) t)
    (he : sphereAction h0 z=lambdaMultiply 6 t) :
    lambdaMultiply 2 (sphereAction h0 z)≠0 := by
  rw [he,lambda_two_six_139 D]
  exact nu_target_lambda_eight_nonzero I SF BHS A qb ab hc3 t ht

end
end KIP126.Computation.SphereAndCofiber
