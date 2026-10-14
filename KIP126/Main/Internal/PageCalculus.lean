module

public import KIP126.Def.SpectralSequence

/-! Representative-level lemmas retained from Selected/ClassicalData at
Kervaire126 bbac1fc05843 (MIT; see the retained source LICENSE). The proof bodies are preserved;
only the internal namespace and local helper names change. -/
@[expose] section
namespace KIP126.Main.Internal
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
universe v
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
theorem nonzero_differential_not_permanent {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q} (hr0 : E.r₀ ≤ r)
    (h : HasNonzeroDifferential E r p q x y) : ¬ NonzeroSurvival E p x := by
  classical
  rintro ⟨z, hz, _⟩
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
  let z' := (Subobject.ofLE (A.Z ⊤) (A.Z n) (A.Z_anti le_top)) z
  obtain ⟨hdeg, xr, yr, hx, hy, hd, hne⟩ := h
  have hr2 := hx.1
  have hlater : ReachesPage E (r + 1) p x := by
    refine ⟨A.pageπ n z', by omega, z', ?_, rfl⟩
    dsimp only [z']
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hd0 := represents_d_zero_of_later hr0 (by omega : r < r + 1) hx hlater
  rw [ModuleCat.comp_apply, hd0, map_zero] at hd
  exact hne hd.symm


theorem earlier_zero_of_target_survives {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    {y : E.Page 2 (p + E.diffDeg r)}
    (hsource : SurvivesTo E r p x)
    (htargets : DifferentialTargets E r p x y)
    (htarget : SurvivesTo E t (p + E.diffDeg r) y) :
    HasDifferential E r p (p + E.diffDeg r) x 0 := by
  classical
  obtain ⟨xr, hxr, _⟩ := hsource
  have hd0 : E.d r p xr = 0 := by
    rcases htargets xr hxr with hz | ⟨yr, hyr, hdr⟩
    · exact hz
    · have hd : HasDifferential E r p (p + E.diffDeg r) x y :=
        ⟨rfl, xr, yr, hxr, hyr, by simpa only [eqToHom_refl, Category.comp_id] using hdr⟩
      have hlater := differential_target_later_zero hr0 hrt hd
      obtain ⟨yt, hyt, hne⟩ := htarget
      exact False.elim (hne (represents_unique hyt hlater))
  exact ⟨rfl, xr, 0, hxr, RepresentsOnPage.zero hxr.1,
    by simpa only [eqToHom_refl, Category.comp_id] using hd0⟩


theorem next_nonzero_of_not_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) (hnot : ¬ HitOnPage E r p x) : a ≠ 0 := by
  classical
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
  have heb : br=b := represents_unique hbr hb
  intro ha0
  have hv := next_projection_zero_iff_incoming E r hr0 q
  have hv' : ∀ zz : (Subobject.underlying.obj (A.Z ↑(r+1-E.r₀).toNat) : ModuleCat ℤ),
      A.pageπ ↑(r+1-E.r₀).toNat zz=0 ↔
        (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
          LinearMap.range (E.d r q).hom := by
    have transport (m : ℕ) (hm : m=(r-E.r₀).toNat+1)
        (hge : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑m) :
        ∀ zz : (Subobject.underlying.obj (A.Z ↑m) : ModuleCat ℤ),
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


theorem permanent_survives_of_no_early_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hstart : E.r₀≤2) (N : ℕ) (hN : 2≤N)
    (hperm : IsPermanentCycle E p x) (hne : x≠0)
    (hnot : ∀ r : ℤ, 2≤r → r<N → ¬HitOnPage E r p x) :
    SurvivesTo E N p x := by
  classical
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
      have han := next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h


theorem nonzero_differential_not_zero {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (h : HasNonzeroDifferential E r p q x y)
    (hzero : HasDifferential E r p q x 0) : False := by
  classical
  obtain ⟨he,a,b,ha,hb,hd,hbn⟩ := h
  obtain ⟨he',a',b',ha',hb',hd'⟩ := hzero
  have haa : a=a' := represents_unique ha ha'
  have hbb : b'=0 := represents_unique hb' (RepresentsOnPage.zero hb'.1)
  apply hbn
  calc b = (E.d r p ≫ eqToHom (congrArg (E.Page r) he)) a := hd.symm
       _ = b' := by simpa only [haa] using hd'
       _ = 0 := hbb


theorem cycle_successor_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0) :
    ∃ zn : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) zn = z := by
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
  exact ⟨zn,hnz⟩


theorem reaches_before {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t) (ht : ReachesPage E t p x) : ReachesPage E r p x := by
  classical
  obtain ⟨a,_,z,hz,_⟩ := ht
  let D := E.ssData p
  have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑(t-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z ↑(t-E.r₀).toNat) (D.Z ↑(r-E.r₀).toNat) (D.Z_anti hrt')) z
  refine ⟨D.pageπ _ zr,hr,zr,?_,rfl⟩
  dsimp only [zr]
  rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz


theorem later_page_frame_of_earlier {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t)
    (hframe : ∃ a : E.Page r p, RepresentsOnPage E r p x a ∧ ∀ y:E.Page r p,y=0∨y=a)
    (ht : ReachesPage E t p x) :
    ∃ a : E.Page t p, RepresentsOnPage E t p x a ∧ ∀ y:E.Page t p,y=0∨y=a := by
  classical
  obtain ⟨ar,har,hall⟩ := hframe
  obtain ⟨at',htrep⟩ := ht
  have htrep' := htrep
  obtain ⟨ht2,z,hzt,hat⟩ := htrep'
  let A := E.ssData p
  let nr : WithTop ℕ := ↑(r-E.r₀).toNat
  let nt : WithTop ℕ := ↑(t-E.r₀).toNat
  have hrt' : nr≤nt := by
    dsimp only [nr,nt]
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let i := Subobject.ofLE (A.Z nt) (A.Z nr) (A.Z_anti hrt')
  have har' : RepresentsOnPage E r p x (A.pageπ nr (i z)) := by
    refine ⟨hr,i z,?_,rfl⟩
    dsimp only [i]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hzt
  have hzr : A.pageπ nr (i z)=ar := represents_unique har' har
  have hzero (w : (Subobject.underlying.obj (A.Z nt) : ModuleCat ℤ))
      (hw : A.pageπ nr (i w)=0) : A.pageπ nt w=0 := by
    apply (subobject_cokernel_π_eq_zero_iff (A.B nt) (A.Z nt) (A.B_le_Z _) _).mpr
    have hh := (subobject_cokernel_π_eq_zero_iff (A.B nr) (A.Z nr) (A.B_le_Z _) _).mp hw
    have he : (A.Z nr).arrow (i w)=(A.Z nt).arrow w :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (A.Z_anti hrt')) w
    rw [he] at hh
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hrt') hh
  refine ⟨at',htrep,?_⟩
  intro y
  haveI : Epi (A.pageπ nt) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨w,hw⟩ := (ModuleCat.epi_iff_surjective (A.pageπ nt)).mp inferInstance y
  rcases hall (A.pageπ nr (i w)) with h0|ha
  · left
    rw [←hw]
    exact hzero w h0
  · right
    have hh : A.pageπ nr (i (w-z))=0 := by rw [map_sub,map_sub,ha,hzr,sub_self]
    have hh' := hzero (w-z) hh
    rw [map_sub,hw,hat,sub_eq_zero] at hh'
    exact hh'



end KIP126.Main.Internal
end
