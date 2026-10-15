module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.SectionSeven.CofiberFiltration
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

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
private theorem d12_criterion_target_basis1_reaches_page1000_for_page_six (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem d12_criterion_d2_s12_t138_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
    exact List.mem_of_getElem? (i := 341) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem d12_criterion_d2_s14_t139_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
    (I.interpretation.basis .sphere 14 139 0) (I.interpretation.basis .sphere 16 140 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,139) (16,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem d12_criterion_target_basis1_reaches_page1000_for_target_survival (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem d12_criterion_nonzero_differential_not_permanent {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q} (hr0 : E.r₀ ≤ r)
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

private theorem d12_criterion_earlier_zero_of_target_survives {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
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

private theorem d12_criterion_next_nonzero_of_not_hit {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
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

private theorem d12_criterion_permanent_survives_of_no_early_hit {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {x : E.Page 2 p}
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
      have han := d12_criterion_next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h

private theorem d12_criterion_nonzero_differential_not_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
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

private theorem d12_criterion_cycle_successor_lift
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
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

private theorem d12_criterion_reaches_before {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
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

private theorem d12_criterion_later_page_frame_of_earlier {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
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

private theorem d12_criterion_target_page_six_frame (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a) ∧
    ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M) := by
  classical
  classical

  have t_label (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
      I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
    have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      exact List.mem_of_getElem? (i := 217) (by rfl)
    have hc := I.monomials _ hmem rfl
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

  have t_page6_frame (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
      ∃ a : (sequence D .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D .sphere) 6 (14,139) (I.interpretation.basis .sphere 14 139 1) a ∧
        ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a := by
    let E := sequence D .sphere
    have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := d12_criterion_target_basis1_reaches_page1000_for_page_six I
    have h341 : HasDifferential E 2 (12,138) (14,139)
        (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := d12_criterion_d2_s12_t138_basis1 I
    have h343 : HasDifferential E 2 (14,139) (16,140)
        (I.interpretation.basis .sphere 14 139 0) (I.interpretation.basis .sphere 16 140 2) := d12_criterion_d2_s14_t139_basis0 I
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
      exact List.mem_of_getElem? (i := 217) (by rfl))
    change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 139 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 139 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 139 2 := he 2
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
      exact List.mem_of_getElem? (i := 231) (by rfl))
    change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 140 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 16 140 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 16 140 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 16 140 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 16 140 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 16 140 4 := hf 4
    obtain ⟨a1000,ha1000⟩ := h342
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤1000) ha1000
    have hz2 : RepresentsOnPage E 6 (14,139) (I.interpretation.basis .sphere 14 139 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h341
    have dz {x : E.Page 2 (14,139)} {b : E.Page 6 (14,139)}
        (hb : RepresentsOnPage E 6 (14,139) x b) : E.d 2 (14,139) x=0 := by
      obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hb
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<6) hb2 ⟨b,hb⟩
      simpa only [hb2.eq_on_page_two] using hh
    have hd0 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 0)=I.interpretation.basis .sphere 16 140 2 := h343.eq_on_page_two.2
    have hd1 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 1)=0 := dz ha
    have hd2 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 2)=0 := dz hz2
    refine ⟨a,ha,?_⟩
    intro y
    let A := E.ssData (14,139)
    haveI : Epi (A.pageπ 4) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 4)).mp inferInstance y
    let x := (Subobject.ofLE (A.Z 4) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤4)) ≫ A.pageπ 0) z
    have hxrep : RepresentsOnPage E 6 (14,139) x y := ⟨by decide,z,rfl,hz⟩
    have hx : E.d 2 (14,139) x=0 := dz hxrep
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe] at hx hxrep
      left
      apply represents_unique hxrep
      exact RepresentsOnPage.zero (by decide)
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      left
      apply represents_unique hxrep
      rw [he2]
      exact hz2
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      right
      apply represents_unique hxrep
      rw [he1]
      exact ha
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
      rw [hxe] at hx hxrep
      right
      apply represents_unique hxrep
      rw [he1,he2]
      simpa only [add_zero] using represents_add_tail ha hz2
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [he0, hd0] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [map_add] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  obtain ⟨a,ha,hall⟩ := t_page6_frame I
  have hlabel := (distinguished_expression_comparisons I).2.2
  have hl : L.target M = I.interpretation.basis .sphere 14 139 1 := hlabel.symm.trans (t_label I)
  constructor
  · exact ⟨a,by rw [hl]; exact ha,hall⟩
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := d12_criterion_target_basis1_reaches_page1000_for_target_survival I
  rw [hl]
  exact h342

private theorem d12_criterion_h6_twelve_outgoing_nonzero
    (h12 : SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      12 (2,128) (Sphere.Internal.hiSquare H M 6))
    (h13 : ¬SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      13 (2,128) (Sphere.Internal.hiSquare H M 6)) :
    ∃ a, RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      12 (2,128) (Sphere.Internal.hiSquare H M 6) a ∧
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d 12 (2,128) a≠0 := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C:=C))
  obtain ⟨a,ha,hane⟩ := h12
  refine ⟨a,ha,?_⟩
  intro hzero
  have ha' := ha
  obtain ⟨_,z,hz2,hza⟩ := ha'
  have hz : E.d 12 (2,128) ((E.ssData (2,128)).pageπ 10 z)=0 := by
    change E.d 12 (2,128) ((E.ssData (2,128)).pageπ ↑(12-E.r₀).toNat z)=0
    rw [hza]
    exact hzero
  obtain ⟨zn,hnz⟩ := d12_criterion_cycle_successor_lift E 12 (by change (2:ℤ)≤12; omega) (2,128) z hz
  let A := E.ssData (2,128)
  change (Subobject.ofLE (A.Z 11) (A.Z 10) (A.Z_anti (by decide : (10:WithTop ℕ)≤11))) zn=z at hnz
  let b := A.pageπ 11 zn
  have hb : RepresentsOnPage E 13 (2,128) (Sphere.Internal.hiSquare H M 6) b := by
    refine ⟨by decide,zn,?_,rfl⟩
    calc
      (Subobject.ofLE (A.Z 11) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤11)) ≫ A.pageπ 0) zn =
        (Subobject.ofLE (A.Z 10) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤10)) ≫ A.pageπ 0)
          ((Subobject.ofLE (A.Z 11) (A.Z 10) (A.Z_anti (by decide : (10:WithTop ℕ)≤11))) zn) := by
          rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
      _ = _ := by rw [hnz]; exact hz2
  have hnot : ¬HitOnPage E 12 (2,128) (Sphere.Internal.hiSquare H M 6) := by
    rintro ⟨q,hq,c,d,hd,hdne,hcd⟩
    have hfst : q.1+12=2 := congrArg Prod.fst hq
    haveI : Subsingleton (E.Page 12 q) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        12 q.1 q.2 (by omega)
    rw [Subsingleton.elim c 0,map_zero] at hcd
    exact hdne hcd.symm
  have hbn : b≠0 := d12_criterion_next_nonzero_of_not_hit (by change (2:ℤ)≤12; omega : E.r₀≤12)
    (by decide : (2:ℤ)≤12) hb ha hane hnot
  exact h13 ⟨b,hb,hbn⟩

private theorem d12_criterion_target_page_twelve_frame (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    ∃ a : (sequence D .sphere).Page 12 (14,139),
      RepresentsOnPage (sequence D .sphere) 12 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 12 (14,139), y=0 ∨ y=a := by
  classical
  obtain ⟨hframe,hreach⟩ := d12_criterion_target_page_six_frame I
  exact d12_criterion_later_page_frame_of_earlier (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤12)
    hframe (d12_criterion_reaches_before (by decide : (2:ℤ)≤12) (by decide : (12:ℤ)≤1000) hreach)

private theorem d12_criterion_survives_twelve_not_thirteen_d12 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (h12 : SurvivesTo (sequence D .sphere)
      12 (2,128) (Sphere.Internal.hiSquare H M 6))
    (h13 : ¬SurvivesTo (sequence D .sphere)
      13 (2,128) (Sphere.Internal.hiSquare H M 6)) : H6SquareSupportsD12 M L := by
  classical
  obtain ⟨a,ha,hdne⟩ := d12_criterion_h6_twelve_outgoing_nonzero h12 h13
  obtain ⟨b,hb,hall⟩ := d12_criterion_target_page_twelve_frame I
  have hdb : (sequence D .sphere).d 12 (2,128) a=b :=
    (hall ((sequence D .sphere).d 12 (2,128) a)).resolve_left hdne
  refine ⟨rfl,a,b,ha,hb,?_,?_⟩
  · simp only [eqToHom_refl,Category.comp_id]
    exact hdb
  · intro hb0
    exact hdne (hdb.trans hb0)

private theorem bx_lambda_nine_not_ten_d12
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (comparison : KIP126.Comparison.ClassicalSynthetic.SphereFirstQuotientComparison H Syn)
    (η : KIP126.Kervaire.SyntheticTheta5.Eta Syn)
    (θ : KIP126.Kervaire.SyntheticTheta5.Theta Syn)
    (hBX : KIP126.Kervaire.BJMOriginalCriterion H M comparison η θ)
    (h9 : KIP126.Synthetic.Context.VanishesModLambda 9
      (KIP126.Kervaire.SyntheticTheta5.etaThetaSquare η θ))
    (h10 : ¬KIP126.Synthetic.Context.VanishesModLambda 10
      (KIP126.Kervaire.SyntheticTheta5.etaThetaSquare η θ)) : H6SquareSupportsD12 M L := by
  classical
  have h12 := (hBX.2.2.2 9 (by omega)).mpr h9

  have h13 : ¬SurvivesTo (sequence D .sphere) 13 (2,128) (Sphere.Internal.hiSquare H M 6) := by
    classical
    intro hh
    exact h10 ((hBX.2.2.2 10 (by omega)).mp hh)

  classical
  exact d12_criterion_survives_twelve_not_thirteen_d12 I h12 h13

private theorem d6_vanishes_iff_target_survives_twelve
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation) :
    Stem126D6Vanishes L ↔ SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) := by
  classical
  have labels := distinguished_expression_comparisons I

  have hW : SurvivesTo (sequence D .sphere) 6 (8,134) L.W := by
    classical
    have hw := SF.w_to_e6
    change SurvivesTo (sequence D .sphere) 6 (8,134) (I.interpretation.sphere 8 134 W) at hw
    rwa [labels.1] at hw

  have htargets : DifferentialTargets (sequence D .sphere) 6 (8,134) L.W (L.target M) := by
    classical
    simpa only [labels.1, labels.2.2] using SF.w_d6_targets

  classical
  constructor
  · intro hc3
    have hp := SF.t_permanent_cycle
    rw [labels.2.2] at hp
    have hn : L.target M≠0 := by
      intro hz
      apply SF.t_not_h0_multiple
      refine ⟨0,?_⟩
      rw [labels.2.2,hz]
      simp only [Sphere.Internal.product,map_zero]
    apply d12_criterion_permanent_survives_of_no_early_hit (by change (2:ℤ)≤2; decide) 12 (by decide) hp hn
    intro r hr hr12 hit
    rw [←labels.2.2] at hit
    rcases SF.t_only_incoming r hit with ⟨he,hd⟩ | ⟨he,_⟩
    · subst r
      change HasNonzeroDifferential (sequence D .sphere) 6 (8,134) (14,139)
        (I.interpretation.sphere 8 134 W) (I.interpretation.sphere 14 139 T) at hd
      rw [labels.1,labels.2.2] at hd
      exact d12_criterion_nonzero_differential_not_zero hd hc3
    · omega
  · intro hs
    exact d12_criterion_earlier_zero_of_target_survives
      (E:=sequence D .sphere) (r:=6) (t:=12)
      (by change (2:ℤ)≤6; decide) (by decide) hW htargets hs

private theorem d12_necessary_from_sphere_facts
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (hd : H6SquareSupportsD12 M L) : ¬ PermanentH6Square M ∧ Stem126D6Vanishes L := by
  classical
  have labels := distinguished_expression_comparisons I

  classical
  refine ⟨?_, ?_⟩
  · exact d12_criterion_nonzero_differential_not_permanent (by change (2 : ℤ) ≤ 12; decide) hd
  · have hW : SurvivesTo (sequence D .sphere) 6 (8,134) L.W := by
      have hw := SF.w_to_e6
      change SurvivesTo (sequence D .sphere) 6 (8,134) (I.interpretation.sphere 8 134 W) at hw
      rwa [labels.1] at hw
    have htargets : DifferentialTargets (sequence D .sphere) 6 (8,134) L.W (L.target M) := by
      simpa only [labels.1, labels.2.2] using SF.w_d6_targets
    exact d12_criterion_earlier_zero_of_target_survives
      (E := sequence D .sphere) (r := 6) (t := 12)
      (by change (2 : ℤ) ≤ 6; decide) (by decide) hW htargets hd.target_survives

private theorem d12_criterion_classical_differentials (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (SF : Derived.SphereFacts I.interpretation) :
    (Stem126D6Vanishes L ↔ SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M)) ∧
    (H6SquareSupportsD12 M L → ¬PermanentH6Square M ∧ Stem126D6Vanishes L) ∧
    (∀ (eta : BiHom 1 2 (S_0_0 : Syn)) (theta : BiHom 62 64 (S_0_0 : Syn)),
      BJMOriginalCriterion H M D.sphereFirstQuotient eta theta →
      VanishesModLambda 9 (sphereProduct eta (sphereProduct theta theta)) →
      ¬VanishesModLambda 10 (sphereProduct eta (sphereProduct theta theta)) → H6SquareSupportsD12 M L) ∧
    ((∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) := by
  classical
  exact ⟨d6_vanishes_iff_target_survives_twelve I SF,d12_necessary_from_sphere_facts I SF,
    fun eta theta h h9 h10=>bx_lambda_nine_not_ten_d12 I D.sphereFirstQuotient eta theta h h9 h10,
    d12_criterion_target_page_six_frame I⟩
end
end KIP126.Main.SectionSeven.DifferentialCriterion
