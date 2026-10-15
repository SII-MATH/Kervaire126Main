module
import all KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Def.ProofTools.Operations
public import KIP126.Def.ProofTools.Representatives
import all KIP126.Main.Internal.DetectionLabels

/-! The last finite differential argument from AlphaOne/ThetaFrames:339–823
at bbac1fc05843 (MIT). Its trigraded naturality proof is the same common
representative argument already proved for the bigraded core. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Literature KIP126.Kervaire.Route
open KIP126.Core KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations
open KIP126.Main.SectionSeven (FiniteNonzeroDifferential)
noncomputable section
universe u v
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private def RawRepresentsOnPage {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) Tridegree)
    (r : ℤ) (p : Tridegree) (x : E.Page 2 p) (y : E.Page r p) : Prop :=
  ∃ hr : 2 ≤ r,
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    ∃ z : (Subobject.underlying.obj (D.Z m) : ModuleCat R),
      (Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti (by
        change (↑(2 - E.r₀).toNat : WithTop ℕ) ≤ ↑(r - E.r₀).toNat
        exact_mod_cast (show (2 - E.r₀).toNat ≤ (r - E.r₀).toNat by omega))) ≫
        D.pageπ n) z = x ∧ D.pageπ m z = y

private def RawHasDifferential {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) Tridegree)
    (r : ℤ) (p q : Tridegree) (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  ∃ h : p + E.diffDeg r = q,
    ∃ (xr : E.Page r p) (yr : E.Page r q),
      RawRepresentsOnPage E r p x xr ∧ RawRepresentsOnPage E r q y yr ∧
        (E.d r p ≫ eqToHom (congrArg (E.Page r) h)) xr = yr

private theorem SSDataMorphism.rawRepresentsOnPage_reindexed
    {E E' : SpectralSequence (ModuleCat.{v} R) Tridegree}
    {τ : Tridegree → Tridegree}
    (f : SSDataMorphism Tridegree E.ssData (fun p => E'.ssData (τ p)))
    (hstart : E.r₀ = E'.r₀) {r : ℤ} {p : Tridegree}
    {x : E.Page 2 p} {y : E.Page r p} (h : RawRepresentsOnPage E r p x y) :
    RawRepresentsOnPage E' r (τ p)
      ((f.pageMap p (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) x)
      ((f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(r - a).toNat : WithTop ℕ)) hstart)) y) := by
  rcases E with ⟨⟨r₀, D, δ, d⟩, dd, Zs, Bs⟩
  rcases E' with ⟨⟨r₀', D', δ', d'⟩, dd', Zs', Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨hr, z, hx, hy⟩ := h
  let n : WithTop ℕ := ↑(2 - r₀).toNat
  let m : WithTop ℕ := ↑(r - r₀).toNat
  have hnm : n ≤ m := by
    dsimp [n, m]
    exact_mod_cast (show (2 - r₀).toNat ≤ (r - r₀).toNat by omega)
  refine ⟨hr, f.cycleMap p m z, ?_, ?_⟩
  · have hs := f.cycleMap_ofLE_assoc p hnm ((D' (τ p)).pageπ n)
    have hp := f.pageπ_pageMap p n
    have heq :
        (Subobject.ofLE ((D p).Z m) ((D p).Z n) ((D p).Z_anti hnm) ≫
          (D p).pageπ n) ≫ f.pageMap p n =
        f.cycleMap p m ≫
          Subobject.ofLE ((D' (τ p)).Z m) ((D' (τ p)).Z n)
            ((D' (τ p)).Z_anti hnm) ≫ (D' (τ p)).pageπ n := by
      rw [Category.assoc, hp]
      exact hs
    have hz := congrArg (fun a => a z) heq
    simpa only [ModuleCat.comp_apply, hx, eqToHom_refl, Category.comp_id, n, m]
      using hz.symm
  · have hz := congrArg (fun a => a z) (f.pageπ_pageMap p m)
    simpa only [ModuleCat.comp_apply, hy, eqToHom_refl, Category.comp_id, n, m]
      using hz.symm

/-- Differential equations transfer along a reindexed ambient morphism whose
induced quotient maps commute with the actual differentials. The reindexing
need only respect each differential translation; it need not be additive.
The commutation premise is a morphism law to be proved for any actual model. -/
private theorem SSDataMorphism.rawHasDifferential_reindexed
    {E E' : SpectralSequence (ModuleCat.{v} R) Tridegree}
    {τ : Tridegree → Tridegree}
    (f : SSDataMorphism Tridegree E.ssData (fun p => E'.ssData (τ p)))
    (hstart : E.r₀ = E'.r₀)
    (hdegree : ∀ (r : ℤ) (p : Tridegree),
      τ (p + E.diffDeg r) = τ p + E'.diffDeg r)
    (hcomm :
      let Φ : ∀ (r : ℤ) (p : Tridegree), E.Page r p ⟶ E'.Page r (τ p) :=
        fun r p => f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
          (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
            (↑(r - a).toNat : WithTop ℕ)) hstart)
      ∀ (r : ℤ) (p : Tridegree),
        Φ r p ≫ E'.d r (τ p) =
          E.d r p ≫ Φ r (p + E.diffDeg r) ≫
            eqToHom (congrArg (E'.Page r) (hdegree r p)))
    {r : ℤ} {p q : Tridegree} {x : E.Page 2 p} {y : E.Page 2 q}
    (h : RawHasDifferential E r p q x y) :
    RawHasDifferential E' r (τ p) (τ q)
      ((f.pageMap p (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) x)
      ((f.pageMap q (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ q)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) y) := by
  let Φ : ∀ (r : ℤ) (p : Tridegree), E.Page r p ⟶ E'.Page r (τ p) :=
    fun r p => f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
      (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
        (↑(r - a).toNat : WithTop ℕ)) hstart)
  change ∀ (r : ℤ) (p : Tridegree),
    Φ r p ≫ E'.d r (τ p) = E.d r p ≫ Φ r (p + E.diffDeg r) ≫
      eqToHom (congrArg (E'.Page r) (hdegree r p)) at hcomm
  change RawHasDifferential E' r (τ p) (τ q) (Φ 2 p x) (Φ 2 q y)
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  have hdeg' : τ p + E'.diffDeg r = τ q :=
    (hdegree r p).symm.trans (congrArg τ hdeg)
  refine ⟨hdeg', Φ r p xr, Φ r q yr, ?_, ?_, ?_⟩
  · exact SSDataMorphism.rawRepresentsOnPage_reindexed f hstart hx
  · exact SSDataMorphism.rawRepresentsOnPage_reindexed f hstart hy
  · have heq : Φ r p ≫ E'.d r (τ p) ≫ eqToHom (congrArg (E'.Page r) hdeg') =
        (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) ≫ Φ r q := by
      rw [← Category.assoc, hcomm, Category.assoc]
      subst q
      simp
    have hz := congrArg (fun a => a xr) heq
    simpa only [ModuleCat.comp_apply, hd] using hz

/-- A common cycle representative maps to a common cycle representative. -/
private theorem SpectralSequenceMorphism.rawRepresentsOnPage
    {E E' : SpectralSequence (ModuleCat.{v} R) Tridegree}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p : Tridegree}
    {x : E.Page 2 p} {y : E.Page r p} (h : RawRepresentsOnPage E r p x y) :
    RawRepresentsOnPage E' r p (f.pageMap 2 p x) (f.pageMap r p y) := by
  convert SSDataMorphism.rawRepresentsOnPage_reindexed f.toSSDataMorphism (E := E) (E' := E')
    (τ := id) f.r₀_eq h using 1 <;> rfl

/-- Differential equations between named E₂ representatives are natural.
The image equation can have zero source or target. -/
private theorem SpectralSequenceMorphism.rawHasDifferential
    {E E' : SpectralSequence (ModuleCat.{v} R) Tridegree}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p q : Tridegree}
    {x : E.Page 2 p} {y : E.Page 2 q} (h : RawHasDifferential E r p q x y) :
    RawHasDifferential E' r p q (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  have hdegree : ∀ (r : ℤ) (p : Tridegree),
      id (p + E.diffDeg r) = id p + E'.diffDeg r := by
    intro r p
    rw [f.diffDeg_eq]
    rfl
  have hf := SSDataMorphism.rawHasDifferential_reindexed f.toSSDataMorphism (E := E) (E' := E')
    (τ := id) f.r₀_eq hdegree (fun r p => by
      convert f.pageMap_comm_d r p using 1 <;> rfl) h
  convert hf using 1 <;> rfl


private theorem finite_last_nonzero_last_cycle_infinity_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree)
    (r : ℤ) (hr : E.r₀ ≤ r) (p : Tridegree)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → E.d j p = 0) :
    ∃ zi : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top)) zi = z := by
  classical
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hsucc : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hsucc)
  have hker : D.pageπ ↑n z ∈ LinearMap.ker (E.d r p).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image] at hker
  obtain ⟨z',hz'⟩ := hker
  change D.pageπ ↑n (i z') = D.pageπ ↑n z at hz'
  have hzero : D.pageπ ↑n (z-i z')=0 := by rw [map_sub,hz',sub_self]
  have hb : ∃ b : (Subobject.underlying.obj (D.B ↑n) : ModuleCat.{v} ℤ),
      (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)) b = z-i z' :=
    (cokernel_π_eq_zero_iff_mem_range _ _).mp hzero
  obtain ⟨b,hb⟩ := hb
  have hBZ : D.B ↑n ≤ D.Z ↑(n+1) := (D.B_mono hsucc).trans (D.B_le_Z _)
  let zn : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ) :=
    z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ) b
  have hnz : i zn=z := by
    dsimp only [zn]
    rw [map_add]
    change i z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ ≫ i) b = z
    dsimp only [i]
    rw [Subobject.ofLE_comp_ofLE,hb]
    abel
  have hn1 : (r+1-E.r₀).toNat=n+1 := by dsimp only [n]; omega
  have hZ : D.Z ⊤ = D.Z ↑(n+1) := by
    have hh := cycles_top_eq_of_d_eq_zero E (r+1) (by omega) p hout
    simpa only [hn1] using hh
  let zi := (Subobject.ofLE (D.Z ↑(n+1)) (D.Z ⊤) hZ.ge) zn
  refine ⟨zi,?_⟩
  dsimp only [zi]
  rw [←CategoryTheory.comp_apply,Subobject.ofLE_comp_ofLE]
  exact hnz



private theorem finite_last_nonzero_normalized_last_cycle_infinity
    (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.E₂ i) (xr : A.Page r i)
    (hx : SyntheticRepresentsOnPage A r i x xr)
    (hd : A.d r i xr = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → A.d j i = 0) :
    ∃ e, HasInfinityRepresentative A 2 i x e := by
  classical
  rcases A with ⟨⟨⟨r₀,S,deg,d⟩,dd,Zs,Bs⟩,hf,hdeg⟩
  dsimp only at hf
  subst r₀
  have hdg : deg=syntheticAdamsRawShift := funext hdeg
  subst deg
  let E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree :=
    ⟨⟨2,S,syntheticAdamsRawShift,d⟩,dd,Zs,Bs⟩
  obtain ⟨hr,z,hz,hzr⟩ := hx
  simp only [SyntheticAdamsSS.d,eqToHom_refl,Category.comp_id] at hd hout
  have hz0 : E.d r i ((E.ssData i).pageπ ↑(r-2).toNat z) = 0 := by
    rw [hzr]
    exact hd
  have ho : ∀ j : ℤ, r+1≤j → E.d j i=0 := hout
  obtain ⟨zi,hzi⟩ := finite_last_nonzero_last_cycle_infinity_lift E r hr i z hz0 ho
  refine ⟨(S i).pageπ ⊤ zi,by norm_num,zi,?_,rfl⟩
  change ((Subobject.ofLE _ _ ((S i).Z_anti le_top)) ≫ (S i).pageπ 0) zi=x
  rw [←hz,←hzi]
  rw [←CategoryTheory.comp_apply]
  dsimp only [E]
  rw [Subobject.ofLE_comp_ofLE_assoc]
  rfl



private theorem finite_last_nonzero_finite_quotient_rep_naturality
    {X Y : SyntheticSpectrum} (f : X ⟶ Y) (r : ℤ) (i : Tridegree)
    (x : (model.family.obj X).E₂ i) (xr : (model.family.obj X).Page r i)
    (hx : SyntheticRepresentsOnPage (model.family.obj X) r i x xr) :
    SyntheticRepresentsOnPage (model.family.obj Y) r i
      (familyPageMap model.family f 2 i x) (familyPageMap model.family f r i xr) :=
  SpectralSequenceMorphism.rawRepresentsOnPage (model.family.map f) hx

private theorem finite_last_nonzero_quotient_family_map_comp
    {X Y Z : SyntheticSpectrum} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap model.family (f ≫ g) r i =
      familyPageMap model.family f r i ≫ familyPageMap model.family g r i :=
  (family_page_comp f g r i).symm

private theorem finite_last_nonzero_quotient_hasDifferential_map
    {X Y : SyntheticSpectrum} (f : X ⟶ Y) (r : ℤ) (i j : Tridegree)
    (x : (model.family.obj X).E₂ i) (y : (model.family.obj X).E₂ j)
    (h : SyntheticHasDifferential (model.family.obj X) r i j x y) :
    SyntheticHasDifferential (model.family.obj Y) r i j
      (familyPageMap model.family f 2 i x) (familyPageMap model.family f 2 j y) :=
  SpectralSequenceMorphism.rawHasDifferential (model.family.map f) h

private theorem finite_last_nonzero_classical_to_finite_equation
    (q r k : ℕ) (hr : 2≤r) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) (y : model.classical.sphere.Page 2 (s+r,t+r-1))
    (h : KIP126.Core.SpectralSequence.HasDifferential
      model.classical.sphere r
      (s,t) (s+r,t+r-1) x y) :
    SyntheticHasDifferential
      (model.family.quotient (S_0_0 : SyntheticSpectrum) q) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      (quotientLabel q s t k x)
      (quotientLabel q (s+r) (t+r-1) (k+(r-1)) y) := by
  classical
  let f : (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj SphereSpectrum) ⟶
      (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  let nx : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using model.comparison.nuE2 .sphere 0 s t k x
  let ny : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj SphereSpectrum))).E₂
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) := by
    simpa only [ClassicalObject.obj,add_zero] using model.comparison.nuE2 .sphere 0 (s+r) (t+r-1) (k+(r-1)) y
  have hnx : familyPageMap model.family f 2 (s,t,t-k) nx = model.comparison.sphereE2 s t k x := by
    exact model.comparison.sphere_nu s t k x
  have hny : familyPageMap model.family f 2 (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) ny =
      model.comparison.sphereE2 (s+r) (t+r-1) (k+(r-1)) y := by
    exact model.comparison.sphere_nu (s+r) (t+r-1) (k+(r-1)) y
  have hs := (KIP126.Literature.Standard.bhs_differentials .sphere 0 s t r k hr x y).mp h
  have hx : familyPageMap model.family (f ≫ XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      nx = quotientLabel q s t k x := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap model.family (XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      (familyPageMap model.family f 2 (s,t,t-k) nx) = _
    rw [hnx]
    rfl
  have hy : familyPageMap model.family (f ≫ XModLambdaN.incl S_0_0 q) 2
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      ny =
      quotientLabel q (s+r) (t+r-1) (k+(r-1)) y := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap model.family (XModLambdaN.incl S_0_0 q) 2 _
      (familyPageMap model.family f 2 _ ny) = _
    rw [hny]
    rfl
  have hs' : SyntheticHasDifferential
      (model.family.obj ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj SphereSpectrum))) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      nx
      ny := by
    convert hs using 1 <;> simp [nx,ny,ClassicalObject.obj]
  have ht := finite_last_nonzero_quotient_hasDifferential_map (f ≫ XModLambdaN.incl S_0_0 q) r
    (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) _ _ hs'
  rw [hx,hy] at ht
  exact ht




private theorem finite_last_nonzero_quotient_nu_infinity_cycles
    (q k : ℕ) (hk : k<q) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (e : ((model.family.quotient (model.nu.functor.obj SphereSpectrum) q).sequence.ssData (s,t,t-k)).eInfty)
    (hx : HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj SphereSpectrum) q)
      2 (s,t,t-k) (finiteTargetLabel model .sphere q s t k x) e) :
    x∈KIP126.Literature.cycles model .sphere ((q:ℤ)-k) (s,t) := by
  have hlabel : nuWeightLabel model .sphere s t (t-k) (by omega) x=targetNuLabel model .sphere s t k x := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have tr (a b : ℕ) (hab : a=b) (he : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 he (targetNuLabel model .sphere s t a x)=targetNuLabel model .sphere s t b x := by
      subst b
      rfl
    exact tr _ k hk' _
  have hh := KIP126.Literature.Standard.eInfinity_finite_labels .sphere q (by omega) s t (t-k)
    (by omega) x e
  rw [hlabel] at hh
  have hc := ((hh.mp hx).choose)
  simpa only [show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega] using hc

private theorem finite_last_nonzero_nonzero_differential_not_cycle
    (r : ℕ) (hr : 2≤r) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) (y : model.classical.sphere.Page 2 (s+r,t+r-1))
    (h : HasNonzeroDifferential model.classical.sphere r (s,t) (s+r,t+r-1) x y) :
    x∉KIP126.Literature.cycles model .sphere r (s,t) := by
  intro hx
  obtain ⟨xnext,hnext⟩ := (KIP126.ProofTools.isCycle_iff_reaches model .sphere ((r:ℤ)+1) (by omega) (s,t) x).mp
    ⟨by omega,by simpa only [add_sub_cancel_right] using hx⟩
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd,hn⟩ := h
  have hz := represents_d_zero_of_later (by rw [model.classical.firstPage]; omega)
    (by omega : (r:ℤ)<(r:ℤ)+1) hxr ⟨xnext,hnext⟩
  apply hn
  rw [←hd]
  change (eqToHom (congrArg (model.classical.sphere.Page r) hdeg)) (model.classical.sphere.d r (s,t) xr)=0
  rw [hz,map_zero]

private theorem finite_last_nonzero
    (q r k : ℕ) (hr : 2≤r) (hqr : q=k+r) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) (y : model.classical.sphere.Page 2 (s+r,t+r-1))
    (h : HasNonzeroDifferential model.classical.sphere r (s,t) (s+r,t+r-1) x y) :
    FiniteNonzeroDifferential q r s t (s+r) (t+r-1) k (k+(r-1)) x y := by
  let A := model.family.quotient (S_0_0 : SyntheticSpectrum) q
  let N := model.family.quotient (model.nu.functor.obj SphereSpectrum) q
  let f := XModLambdaN.map model.nu.unitIso.inv q
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := finite_last_nonzero_classical_to_finite_equation q r k hr s t x y h.toHasDifferential
  refine ⟨hdeg,xr,yr,hx,hy,hd,?_⟩
  intro hyr
  have hz : A.sequence.d r (s,t,t-k) xr=0 := by
    have hi := (ModuleCat.mono_iff_injective (eqToHom (congrArg (A.Page r) hdeg))).mp inferInstance
    apply hi
    change (A.sequence.d r (s,t,t-k) ≫ eqToHom (congrArg (A.Page r) hdeg)) xr=_
    rw [hd,hyr,map_zero]
  let nxr := familyPageMap model.family f r (s,t,t-k) xr
  have hnx : SyntheticRepresentsOnPage N r (s,t,t-k) (finiteTargetLabel model .sphere q s t k x) nxr := by
    have hh := finite_last_nonzero_finite_quotient_rep_naturality f r (s,t,t-k) (quotientLabel q s t k x) xr hx
    rw [sphere_quotient_label_to_nu] at hh
    exact hh
  have hnz : N.d r (s,t,t-k) nxr=0 := by
    have hh := congrArg (fun a => a xr) ((model.family.map f).pageMap_comm_d r (s,t,t-k))
    simp only [ModuleCat.comp_apply] at hh
    change N.sequence.d r (s,t,t-k) nxr =
      ((eqToHom _ : N.Page r ((s,t,t-k)+A.sequence.diffDeg r) ⟶ N.Page r ((s,t,t-k)+N.sequence.diffDeg r)))
        ((model.family.map f).pageMap r _ (A.sequence.d r (s,t,t-k) xr)) at hh
    rw [hz,map_zero,map_zero] at hh
    change (N.sequence.d r (s,t,t-k) ≫ eqToHom _) nxr=0
    rw [ModuleCat.comp_apply,hh,map_zero]
  have hout : ∀ j : ℤ, (r:ℤ)+1≤j → N.d j (s,t,t-k)=0 := by
    intro j hj
    have hv := KIP126.Literature.Standard.finite_quotient_vanishing .sphere q (by omega) j (by omega)
      (s+j) (t+(j-1)) (t-k) (Or.inr (by omega))
    have ht : (s,t,t-k)+syntheticAdamsRawShift j=(s+j,t+(j-1),t-k) := by
      simp [syntheticAdamsRawShift]
    haveI : Subsingleton (N.Page j ((s,t,t-k)+syntheticAdamsRawShift j)) := by
      rw [ht]
      exact ModuleCat.subsingleton_of_isZero hv
    ext z
    exact Subsingleton.elim _ _
  obtain ⟨e,he⟩ := finite_last_nonzero_normalized_last_cycle_infinity N r (s,t,t-k) _ nxr hnx hnz hout
  have hc := finite_last_nonzero_quotient_nu_infinity_cycles q k (by omega) s t x e he
  rw [show (q:ℤ)-k=(r:ℤ) by omega] at hc
  exact finite_last_nonzero_nonzero_differential_not_cycle r hr s t x y h hc

end
end KIP126.Main.Internal.AlphaOne
