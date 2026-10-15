module

public import KIP126.Main.SectionSeven.NuExtension.FifthQuotient

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

section NuNinthProof
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra KIP126.Literature.AdamsSynthetic KIP126.Computation.SphereAndCofiber
open KIP126.Algebra KIP126.LinE2 PageRepresentatives
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}

section
attribute [local irreducible] adamsTowerSSData
private theorem nu9_not_boundary (X : C) (p : ℤ×ℤ)
    (x : Ambient H X p) (hx : x≠0)
    (b : ℤ) (hb : 1≤b)
    (hn : NeverHitOnWindow (adamsTowerInternalSpectralSequence H.unit X) 2 b p x) :
    x ∉ boundaries H X b p := by
  have nhb_represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b) : a = b := by
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
  have nhb_represents_smul {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (c : ℤ) :
      KIP126.SpectralSequence.RepresentsOnPage E r p (c • x) (c • a) := by
    obtain ⟨hr, z, hz, hza⟩ := ha
    refine ⟨hr, c • z, ?_, ?_⟩ <;> simp only [map_zsmul, hz, hza]
  have nhb_represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a)
      (ht : KIP126.SpectralSequence.ReachesPage E t p x) : E.d r p a = 0 := by
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
    have hrep : KIP126.SpectralSequence.RepresentsOnPage E r p x (D'.pageπ nr zr) := by
      refine ⟨ha.1, zr, ?_, rfl⟩
      dsimp only [zr]
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      exact hz
    rw [nhb_represents_unique ha hrep]
    change D'.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
    rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
    refine ⟨(Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z, ?_⟩
    change (Subobject.ofLE (D'.Z ns) (D'.Z nr) (D'.Z_anti hrs) ≫ D'.pageπ nr)
      ((Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z) = D'.pageπ nr zr
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  have nhb_next_projection_zero_iff_incoming
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
      (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
      (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
        ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ)) :
      (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
        (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
          (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
            (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
          LinearMap.range (E.d r p).hom := by
    let D' := E.ssData (p+E.diffDeg r)
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    let i := Subobject.ofLE (D'.Z ↑(n+1)) (D'.Z ↑n) (D'.Z_anti hnm)
    let j := Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑n)
      ((D'.B_le_Z _).trans (D'.Z_anti hnm))
    rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
    change D'.pageπ ↑(n+1) z = 0 ↔ (i ≫ D'.pageπ ↑n) z ∈ LinearMap.range (j ≫ D'.pageπ ↑n).hom
    constructor
    · intro hz
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _)) z).mp hz
      refine ⟨v, ?_⟩
      rw [← hv]
      change (j ≫ D'.pageπ ↑n) v =
        ((Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _)) ≫ i ≫ D'.pageπ ↑n) v
      congr 2
      dsimp only [i,j]
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    · rintro ⟨v, hv⟩
      apply (subobject_cokernel_π_eq_zero_iff (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _) z).mpr
      have hz : D'.pageπ ↑n (i z-j v) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hv.symm
      have hb := (subobject_cokernel_π_eq_zero_iff (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z _) _).mp hz
      have hb' := (ModuleCat.subobjectModule D'.V).monotone (D'.B_mono hnm) hb
      have hv' : (D'.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D'.V) (D'.B ↑(n+1)) := by
        change (j ≫ (D'.Z ↑n).arrow) v ∈ _
        dsimp only [j]
        rw [Subobject.ofLE_arrow]
        exact ⟨v, rfl⟩
      have hh := ((ModuleCat.subobjectModule D'.V) (D'.B ↑(n+1))).add_mem hb' hv'
      rw [map_sub, sub_add_cancel] at hh
      change (i ≫ (D'.Z ↑n).arrow) z ∈ _ at hh
      dsimp only [i] at hh
      rwa [Subobject.ofLE_arrow] at hh
  have nhb_zero_successor_has_incoming
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
      (r : ℤ) (hr : 2 ≤ r) (hr0 : E.r₀ ≤ r)
      (p : ℤ × ℤ) (x : E.Page 2 p)
      (hy : KIP126.SpectralSequence.RepresentsOnPage E (r+1) p x 0) :
      ∃ (a : E.Page r p), KIP126.SpectralSequence.RepresentsOnPage E r p x a ∧
        ∃ (q : ℤ × ℤ) (hq : q+E.diffDeg r=p) (z : E.Page r q),
          (E.d r q ≫ eqToHom (congrArg (E.Page r) hq)) z=a := by
    generalize hq : p-E.diffDeg r=q
    have he : q+E.diffDeg r=p := by rw [←hq,sub_add_cancel]
    subst p
    let A := E.ssData (q+E.diffDeg r)
    let nr : WithTop ℕ := ↑(r-E.r₀).toNat
    let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
    let n0 : WithTop ℕ := ↑(2-E.r₀).toNat
    have ht : (r+1-E.r₀).toNat=(r-E.r₀).toNat+1 := by omega
    have h0s : n0 ≤ ns := by
      dsimp only [n0,ns]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
    have hrep : ∃ z : (Subobject.underlying.obj (A.Z ns) : ModuleCat.{v} ℤ),
        (Subobject.ofLE (A.Z ns) (A.Z n0) (A.Z_anti h0s) ≫ A.pageπ n0) z=x ∧
        A.pageπ ns z=0 := by
      let P (m : ℕ) : Prop := ∃ hm : n0 ≤ (m : WithTop ℕ),
        ∃ z : (Subobject.underlying.obj (A.Z (m : WithTop ℕ)) : ModuleCat.{v} ℤ),
          (Subobject.ofLE (A.Z (m : WithTop ℕ)) (A.Z n0) (A.Z_anti hm) ≫ A.pageπ n0) z=x ∧
          A.pageπ (m : WithTop ℕ) z=(0 : A.page (m : WithTop ℕ))
      have hP : P (r+1-E.r₀).toNat := by
        refine ⟨?_,hy.2⟩
        dsimp only [n0]
        exact_mod_cast (show (2-E.r₀).toNat ≤ (r+1-E.r₀).toNat by omega)
      have hP' : P ((r-E.r₀).toNat+1) := ht ▸ hP
      obtain ⟨hm,z,hz,hzero⟩ := hP'
      exact ⟨z,hz,hzero⟩
    obtain ⟨z,hz,hzero⟩ := hrep
    let zr := (Subobject.ofLE (A.Z ns) (A.Z nr) (A.Z_anti
      (by dsimp only [nr,ns]; exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) z
    let a := A.pageπ nr zr
    have ha : KIP126.SpectralSequence.RepresentsOnPage E r (q+E.diffDeg r) x a := by
      refine ⟨hr,zr,?_,rfl⟩
      dsimp only [zr]
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz
    obtain ⟨v,hv⟩ := (nhb_next_projection_zero_iff_incoming E r hr0 q z).mp hzero
    refine ⟨a,ha,q,rfl,v,?_⟩
    simpa only [eqToHom_refl,Category.comp_id,a,zr,A,nr,ns,CategoryTheory.comp_apply] using hv
  have nhb_never_hit_representative_nonzero
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)) (hs : E.r₀=2)
      (p : ℤ × ℤ) (x : E.Page 2 p) (hx : x≠0) (last : ℤ)
      (hn : NeverHitOnWindow E 2 last p x) :
      ∀ n : ℕ, (n:ℤ)+1 ≤ last → ∀ a : E.Page ((n:ℤ)+2) p,
        KIP126.SpectralSequence.RepresentsOnPage E ((n:ℤ)+2) p x a → a≠0 := by
    intro n
    induction n with
    | zero =>
      intro _ a ha hz
      have hh := ha.eq_on_page_two
      exact hx (hh.trans hz)
    | succ n ih =>
      intro hlast a ha hz
      rw [hz] at ha
      have he : ((n+1:ℕ):ℤ)+2=((n:ℤ)+2)+1 := by omega
      rw [he] at ha
      obtain ⟨b,hb,q,hq,z,hd⟩ := nhb_zero_successor_has_incoming E ((n:ℤ)+2)
        (by omega) (by rw [hs]; omega) p x ha
      exact hn.2.2 ((n:ℤ)+2) (by omega) (by omega)
        ⟨q,hq,z,b,hb,ih (by omega) b hb,hd⟩
  have nhb_represents_zero_iff_boundary (X : C) (r : ℤ) (hr : 2≤r)
      (p : ℤ×ℤ) (x : PageRepresentatives.Ambient H X p) :
      KIP126.SpectralSequence.RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x 0 ↔
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
  have nhb_never_hit_not_boundary_nat (X : C) (p : ℤ×ℤ)
      (x : Ambient H X p) (hx : x≠0) (b : ℕ)
      (hn : NeverHitOnWindow (adamsTowerInternalSpectralSequence H.unit X)
        2 ((b:ℤ)+1) p x) :
      x ∉ boundaries H X ((b:ℤ)+1) p := by
    intro hb
    have hr : 2≤(b:ℤ)+2 := by omega
    have rep : KIP126.SpectralSequence.RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X)
        ((b:ℤ)+2) p x 0 := by
      apply (nhb_represents_zero_iff_boundary X ((b:ℤ)+2) hr p x).mpr
      simpa only [show (b:ℤ)+2-1=(b:ℤ)+1 by omega] using hb
    exact nhb_never_hit_representative_nonzero
      (adamsTowerInternalSpectralSequence H.unit X) rfl p x hx ((b:ℤ)+1)
      hn b (by omega) 0 rep rfl
  have nhb_never_hit_not_boundary (X : C) (p : ℤ×ℤ)
      (x : Ambient H X p) (hx : x≠0) (b : ℤ) (hb : 1≤b)
      (hn : NeverHitOnWindow (adamsTowerInternalSpectralSequence H.unit X) 2 b p x) :
      x ∉ boundaries H X b p := by
    have he : ((b-1).toNat:ℤ)+1=b := by omega
    have hn' : NeverHitOnWindow (adamsTowerInternalSpectralSequence H.unit X)
        2 (((b-1).toNat:ℤ)+1) p x := by
      simpa only [he] using hn
    simpa only [he] using nhb_never_hit_not_boundary_nat X p x hx (b-1).toNat hn'
  exact nhb_never_hit_not_boundary X p x hx b hb hn
end
section
attribute [local irreducible] adamsTowerSSData KIP126.LinE2.homogeneousPart
private theorem nu9_error_data (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    Subsingleton (CycleQuotient H SphereSpectrum 2 8 (12,137)) ∧
    I'.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
    ∀ x : KIP126.Computation.SphereAndCofiber.Page D' .sphere 13 138,
      x ∈ boundaries H SphereSpectrum 9 (13,138) ∨
      x - I'.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 9 (13,138) := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b) : a = b := by
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
  have represents_smul {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (c : ℤ) :
      KIP126.SpectralSequence.RepresentsOnPage E r p (c • x) (c • a) := by
    obtain ⟨hr, z, hz, hza⟩ := ha
    refine ⟨hr, c • z, ?_, ?_⟩ <;> simp only [map_zsmul, hz, hza]
  have represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a)
      (ht : KIP126.SpectralSequence.ReachesPage E t p x) : E.d r p a = 0 := by
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
    have hrep : KIP126.SpectralSequence.RepresentsOnPage E r p x (D'.pageπ nr zr) := by
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
    let D' := E.ssData (p+E.diffDeg r)
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    let i := Subobject.ofLE (D'.Z ↑(n+1)) (D'.Z ↑n) (D'.Z_anti hnm)
    let j := Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑n)
      ((D'.B_le_Z _).trans (D'.Z_anti hnm))
    rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
    change D'.pageπ ↑(n+1) z = 0 ↔ (i ≫ D'.pageπ ↑n) z ∈ LinearMap.range (j ≫ D'.pageπ ↑n).hom
    constructor
    · intro hz
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _)) z).mp hz
      refine ⟨v, ?_⟩
      rw [← hv]
      change (j ≫ D'.pageπ ↑n) v =
        ((Subobject.ofLE (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _)) ≫ i ≫ D'.pageπ ↑n) v
      congr 2
      dsimp only [i,j]
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    · rintro ⟨v, hv⟩
      apply (subobject_cokernel_π_eq_zero_iff (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _) z).mpr
      have hz : D'.pageπ ↑n (i z-j v) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hv.symm
      have hb := (subobject_cokernel_π_eq_zero_iff (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z _) _).mp hz
      have hb' := (ModuleCat.subobjectModule D'.V).monotone (D'.B_mono hnm) hb
      have hv' : (D'.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D'.V) (D'.B ↑(n+1)) := by
        change (j ≫ (D'.Z ↑n).arrow) v ∈ _
        dsimp only [j]
        rw [Subobject.ofLE_arrow]
        exact ⟨v, rfl⟩
      have hh := ((ModuleCat.subobjectModule D'.V) (D'.B ↑(n+1))).add_mem hb' hv'
      rw [map_sub, sub_add_cancel] at hh
      change (i ≫ (D'.Z ↑n).arrow) z ∈ _ at hh
      dsimp only [i] at hh
      rwa [Subobject.ofLE_arrow] at hh
  have page_generated_from_representatives
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r)
      {N : ℕ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ KIP126.Algebra.F2))
      (v : Fin N → E.Page r p)
      (hv : ∀ i, KIP126.SpectralSequence.RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) (v i))
      (a : E.Page r p) :
      ∃ c : Fin N → KIP126.Algebra.F2, a = ∑ i, if c i = 0 then 0 else v i := by
    classical
    have hadd {x y : E.Page 2 p} {xr yr : E.Page r p}
        (hx : KIP126.SpectralSequence.RepresentsOnPage E r p x xr) (hy : KIP126.SpectralSequence.RepresentsOnPage E r p y yr) :
        KIP126.SpectralSequence.RepresentsOnPage E r p (x+y) (xr+yr) := by
      obtain ⟨hr, zx, hx, hxr⟩ := hx
      obtain ⟨_, zy, hy, hyr⟩ := hy
      exact ⟨hr, zx+zy, by rw [map_add,hx,hy], by rw [map_add,hxr,hyr]⟩
    let D' := E.ssData p
    let n : WithTop ℕ := ↑(r-E.r₀).toNat
    haveI : Epi (D'.pageπ n) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D'.pageπ n)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (D'.Z_anti (by
      dsimp only [n]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega))) ≫ D'.pageπ _) z
    have hxa : KIP126.SpectralSequence.RepresentsOnPage E r p x a := ⟨hr,z,rfl,hz⟩
    let c : Fin N → KIP126.Algebra.F2 := e x
    have hsum (s : Finset (Fin N)) :
        KIP126.SpectralSequence.RepresentsOnPage E r p
          (∑ i ∈ s, if c i = 0 then 0 else e.symm (Finsupp.single i 1))
          (∑ i ∈ s, if c i = 0 then 0 else v i) := by
      induction s using Finset.induction_on with
      | empty => simpa using (KIP126.SpectralSequence.RepresentsOnPage.zero (E := E) (p := p) hr)
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        apply hadd _ ih
        by_cases hc : c i = 0
        · simpa only [hc,ite_true] using (KIP126.SpectralSequence.RepresentsOnPage.zero (E := E) (p := p) hr)
        · simpa only [hc,ite_false] using hv i
    have hx : (∑ i : Fin N, if c i = 0 then 0 else e.symm (Finsupp.single i 1)) = x := by
      apply e.injective
      rw [map_sum]
      ext i
      simp only [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · change (e (if c i = 0 then 0 else e.symm (Finsupp.single i 1))) i = c i
        generalize c i = b
        fin_cases b
        · change (e 0) i = 0
          simp
        · change (e (e.symm (Finsupp.single i 1))) i = 1
          simp
      · intro j hj hji
        by_cases hc : c j = 0
        · simp [hc]
        · simp [hc,hji]
      · simp
    refine ⟨c, represents_unique hxa ?_⟩
    have hh := hsum Finset.univ
    simpa only [hx] using hh
  have represents_before
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
      {x : E.Page 2 p} {xt : E.Page t p}
      (hr : 2 ≤ r) (hrt : r ≤ t) (ht : KIP126.SpectralSequence.RepresentsOnPage E t p x xt) :
      ∃ xr, KIP126.SpectralSequence.RepresentsOnPage E r p x xr := by
    obtain ⟨_, z, hz, _⟩ := ht
    let D' := E.ssData p
    have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(t-E.r₀).toNat := by
      exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
    let zr := (Subobject.ofLE (D'.Z ↑(t-E.r₀).toNat) (D'.Z ↑(r-E.r₀).toNat) (D'.Z_anti hrt')) z
    refine ⟨D'.pageπ _ zr, hr, zr, ?_, rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have next_page_two_of_kernel
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)) (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
      (v : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ))
      (hcases : ∀ a : E.Page r p, E.d r p a = 0 → a = 0 ∨
        a = (Subobject.ofLE _ _ ((E.ssData p).Z_anti
          (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
            (E.ssData p).pageπ ↑(r-E.r₀).toNat) v) :
      ∀ a : ((E.ssData p).page ↑((r-E.r₀).toNat+1) : ModuleCat.{v} ℤ),
        a = 0 ∨ a = (E.ssData p).pageπ ↑((r-E.r₀).toNat+1) v := by
    let D' := E.ssData p
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    let i := Subobject.ofLE (D'.Z ↑(n+1)) (D'.Z ↑n) (D'.Z_anti hnm)
    let down := i ≫ D'.pageπ ↑n
    have hzero (z : (Subobject.underlying.obj (D'.Z ↑(n+1)) : ModuleCat.{v} ℤ))
        (hz : down z = 0) : D'.pageπ ↑(n+1) z = 0 := by
      apply (subobject_cokernel_π_eq_zero_iff (D'.B ↑(n+1)) (D'.Z ↑(n+1)) (D'.B_le_Z _) _).mpr
      have hb := (subobject_cokernel_π_eq_zero_iff (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z _) (i z)).mp hz
      change (i ≫ (D'.Z ↑n).arrow) z ∈ _ at hb
      dsimp only [i] at hb
      rw [Subobject.ofLE_arrow] at hb
      exact (ModuleCat.subobjectModule D'.V).monotone (D'.B_mono hnm) hb
    intro a
    haveI : Epi (D'.pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (D'.pageπ ↑(n+1))).mp inferInstance a
    have hcycle : E.d r p (down z) = 0 := by
      change down z ∈ LinearMap.ker (E.d r p).hom
      rw [← subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image]
      exact ⟨z,rfl⟩
    obtain hz | hz := hcases (down z) hcycle
    · exact Or.inl (hzero z hz)
    · right
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply hzero
      rw [map_sub,hz,sub_self]
  have represents_next_nonzero_of_incoming_zero
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
      (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
      (hin : E.d r (p-E.diffDeg r) = 0)
      {x : E.Page 2 p} {a : E.Page (r+1) p} {b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E (r+1) p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b)
      (hne : b ≠ 0) : a ≠ 0 := by
    obtain ⟨_, z, hz, hza⟩ := ha
    let D' := E.ssData p
    let n : WithTop ℕ := ↑(r-E.r₀).toNat
    let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
    have hnm : n ≤ m := by
      dsimp only [n,m]
      exact_mod_cast (show (r-E.r₀).toNat ≤ (r+1-E.r₀).toNat by omega)
    have hB : D'.B m = D'.B n := by
      have hh := boundaries_succ_of_zero E r hr0 (p-E.diffDeg r) hin
      have hi : (r+1-E.r₀).toNat = (r-E.r₀).toNat+1 := by omega
      have hp : p-E.diffDeg r+E.diffDeg r = p := by abel
      rw [hp] at hh
      simpa only [D',n,m,hi] using hh
    let i := Subobject.ofLE (D'.Z m) (D'.Z n) (D'.Z_anti hnm)
    have hb' : KIP126.SpectralSequence.RepresentsOnPage E r p x (D'.pageπ n (i z)) := by
      refine ⟨hr,i z,?_,rfl⟩
      change ((Subobject.ofLE _ _ (D'.Z_anti hnm)) ≫
        Subobject.ofLE _ _ _ ≫ D'.pageπ _) z = x
      rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz
    intro ha0
    apply hne
    rw [represents_unique hb hb']
    apply (subobject_cokernel_π_eq_zero_iff (D'.B n) (D'.Z n) (D'.B_le_Z n) _).mpr
    have hm := (subobject_cokernel_π_eq_zero_iff (D'.B m) (D'.Z m) (D'.B_le_Z m) z).mp (hza.trans ha0)
    rw [hB] at hm
    change (i ≫ (D'.Z n).arrow) z ∈ _
    dsimp only [i]
    rwa [Subobject.ofLE_arrow]
  have differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {t : ℤ} {q : ℤ×ℤ} {y : E.Page 2 q} {x : E.Page 2 p}
      (hr0 : E.r₀ ≤ r) (hrt : r < t)
      (h : KIP126.SpectralSequence.HasDifferential E r p q x y) : KIP126.SpectralSequence.RepresentsOnPage E t q y 0 := by
    obtain ⟨rfl, xr, yr, hx, hy, hd⟩ := h
    simp only [eqToHom_refl, Category.comp_id] at hd
    obtain ⟨hr, z, hz2, hzr⟩ := hy
    let A := E.ssData (p + E.diffDeg r)
    let n : ℕ := (r-E.r₀).toNat
    let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
    let m : WithTop ℕ := ↑(t-E.r₀).toNat
    have hnm : (↑(n+1) : WithTop ℕ) ≤ m := by
      dsimp only [n,m]
      exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
    have hn0 : n₀ ≤ ↑n := by
      dsimp only [n₀,n]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
    have hn1 : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    have hdmem : yr ∈ LinearMap.range (E.d r p).hom := ⟨xr, hd⟩
    rw [← subobjectModule_image, E.B_succ r p hr0, subobjectModule_image] at hdmem
    obtain ⟨b, hb⟩ := hdmem
    let j := Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑n)
      ((A.B_le_Z _).trans (A.Z_anti hn1))
    have hb' : A.pageπ ↑n (j b) = yr := hb
    have hdif : A.pageπ ↑n (z-j b) = 0 := by rw [map_sub, hzr, hb', sub_self]
    have hmem := (subobject_cokernel_π_eq_zero_iff (A.B ↑n) (A.Z ↑n) (A.B_le_Z _) _).mp hdif
    have hmem' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono hn1) hmem
    have hj : (A.Z ↑n).arrow (j b) ∈ (ModuleCat.subobjectModule A.V) (A.B ↑(n+1)) := by
      change (j ≫ (A.Z ↑n).arrow) b ∈ _
      dsimp only [j]
      rw [Subobject.ofLE_arrow]
      exact ⟨b,rfl⟩
    have hzmem := ((ModuleCat.subobjectModule A.V) (A.B ↑(n+1))).add_mem hmem' hj
    rw [map_sub, sub_add_cancel] at hzmem
    obtain ⟨b', hb'⟩ := hzmem
    let i := Subobject.ofLE (A.B ↑(n+1)) (A.Z m) ((A.B_mono hnm).trans (A.B_le_Z _))
    refine ⟨by omega, i b', ?_, ?_⟩
    · have he : (Subobject.ofLE (A.Z m) (A.Z n₀) (A.Z_anti (hn0.trans (hn1.trans hnm))))
          (i b') = (Subobject.ofLE (A.Z ↑n) (A.Z n₀) (A.Z_anti hn0)) z := by
        apply (ModuleCat.mono_iff_injective (A.Z n₀).arrow).mp inferInstance
        change (i ≫ Subobject.ofLE (A.Z m) (A.Z n₀) _ ≫ (A.Z n₀).arrow) b' =
          (Subobject.ofLE (A.Z ↑n) (A.Z n₀) _ ≫ (A.Z n₀).arrow) z
        simpa only [Category.assoc, i, Subobject.ofLE_arrow] using hb'
      exact (congrArg (fun v => A.pageπ n₀ v) he).trans hz2
    · apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
      change (i ≫ (A.Z m).arrow) b' ∈ _
      dsimp only [i]
      rw [Subobject.ofLE_arrow]
      exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) ⟨b',rfl⟩
  have boundary_of_zero_representative
      {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
      (hx : KIP126.SpectralSequence.RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
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
  have middle_add {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hy : KIP126.SpectralSequence.RepresentsOnPage E r p y b) :
      KIP126.SpectralSequence.RepresentsOnPage E r p (x+y) (a+b) := by
    obtain ⟨hr,z,hz,ha⟩ := hx
    obtain ⟨_,w,hw,hb⟩ := hy
    exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
  have middle_if {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : KIP126.SpectralSequence.RepresentsOnPage E r p x a) :
      KIP126.SpectralSequence.RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact KIP126.SpectralSequence.RepresentsOnPage.zero h.1
    · exact h
  have middle_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    ext i
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · generalize f i=b
      fin_cases b <;> simp
    · intro j hj hji
      by_cases hf : f j=0
      · simp [hf]
      · simp [hf,hji]
    · simp
  have middle_rep2 {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
      {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r)
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) : KIP126.SpectralSequence.RepresentsOnPage E 2 p x x := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have nu9_af12_kernel (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
      (x : Page D' .sphere 12 137)
      (dx : (sequence D' .sphere).d 2 (12,137) x = 0) :
      KIP126.SpectralSequence.RepresentsOnPage (sequence D' .sphere) 4 (12,137) x 0 := by
    let E := sequence D' .sphere
    have h260 : KIP126.SpectralSequence.HasDifferential E 2 (10,136) (12,137)
        ((I'.interpretation.basis .sphere 10 136 0)) ((I'.interpretation.basis .sphere 12 137 2)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
        unfold Raw.claims
        iterate 260 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 2 (10,136) (12,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h234 : KIP126.SpectralSequence.HasDifferential E 3 (9,135) (12,137)
        ((I'.interpretation.basis .sphere 9 135 3)) ((I'.interpretation.basis .sphere 12 137 3)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
        unfold Raw.claims
        iterate 234 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 3 (9,135) (12,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h307 : KIP126.SpectralSequence.HasDifferential E 3 (9,135) (12,137)
        ((I'.interpretation.basis .sphere 9 135 0) + (I'.interpretation.basis .sphere 9 135 3)) ((I'.interpretation.basis .sphere 12 137 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
        unfold Raw.claims
        iterate 307 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 3 (9,135) (12,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h308 : KIP126.SpectralSequence.HasDifferential E 2 (12,137) (14,138)
        ((I'.interpretation.basis .sphere 12 137 1)) ((I'.interpretation.basis .sphere 14 138 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
        unfold Raw.claims
        iterate 308 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 2 (12,137) (14,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h309 : KIP126.SpectralSequence.HasDifferential E 2 (12,137) (14,138)
        ((I'.interpretation.basis .sphere 12 137 0)) ((I'.interpretation.basis .sphere 14 138 3)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
        unfold Raw.claims
        iterate 309 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 2 (12,137) (14,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
      unfold Raw.degrees
      iterate 201 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 12 137 i.val at he
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
      unfold Raw.degrees
      iterate 216 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 14 138 i.val at hf
    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 12 137 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 12 137 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 12 137 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 12 137 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 12 137 4 := he 4
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 14 138 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 14 138 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 14 138 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 14 138 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 14 138 4 := hf 4
    have hz2 : KIP126.SpectralSequence.RepresentsOnPage E 4 (12,137) (I'.interpretation.basis .sphere 12 137 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
    have d2 : E.d 2 (12,137) (I'.interpretation.basis .sphere 12 137 2)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
        (middle_rep2 (by decide) hz2) ⟨0,hz2⟩
    have hz3 : KIP126.SpectralSequence.RepresentsOnPage E 4 (12,137) (I'.interpretation.basis .sphere 12 137 3) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
    have d3 : E.d 2 (12,137) (I'.interpretation.basis .sphere 12 137 3)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
        (middle_rep2 (by decide) hz3) ⟨0,hz3⟩
    have hz4 : KIP126.SpectralSequence.RepresentsOnPage E 4 (12,137) (I'.interpretation.basis .sphere 12 137 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
    have d4 : E.d 2 (12,137) (I'.interpretation.basis .sphere 12 137 4)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
        (middle_rep2 (by decide) hz4) ⟨0,hz4⟩
    have d0 : E.d 2 (12,137) (I'.interpretation.basis .sphere 12 137 0)=I'.interpretation.basis .sphere 14 138 3 := h309.eq_on_page_two.2
    have d1 : E.d 2 (12,137) (I'.interpretation.basis .sphere 12 137 1)=I'.interpretation.basis .sphere 14 138 4 := h308.eq_on_page_two.2
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (middle_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
    have hd := congrArg (E.d 2 (12,137)) hcoef
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,d3,d4,ite_self,add_zero] at hd
    have c0 : c 0=0 := by
      by_contra h0
      simp only [h0,ite_false] at hd
      by_cases h1 : c 1=0
      all_goals simp only [h1,ite_true,ite_false] at hd
      all_goals have hh := congrArg (fun z => f z 3) hd
      all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
      all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have c1 : c 1=0 := by
      by_contra h1
      simp only [c0,h1,ite_true,ite_false,zero_add] at hd
      have hh := congrArg (fun z => f z 4) hd
      simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply] at hh
    rw [hcoef]
    simp only [c0,c1,ite_true,zero_add]
    have hh := middle_add (middle_if (c 2) hz2) (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4))
    simpa only [ite_self,zero_add] using hh
  have nu9_af13_cosets (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      I'.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
      ∀ x : Page D' .sphere 13 138,
        x ∈ boundaries H SphereSpectrum 4 (13,138) ∨
        x - I'.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 4 (13,138) := by
    let E := sequence D' .sphere
    have h231 : KIP126.SpectralSequence.HasDifferential E 4 (9,135) (13,138)
        ((I'.interpretation.basis .sphere 9 135 2)) ((I'.interpretation.basis .sphere 13 138 0)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
        unfold Raw.claims
        iterate 231 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 4 (9,135) (13,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h232 : KIP126.SpectralSequence.HasDifferential E 4 (9,135) (13,138)
        ((I'.interpretation.basis .sphere 9 135 1)) ((I'.interpretation.basis .sphere 13 138 2)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
        unfold Raw.claims
        iterate 232 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 4 (9,135) (13,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h288 : KIP126.SpectralSequence.HasDifferential E 2 (11,137) (13,138)
        ((I'.interpretation.basis .sphere 11 137 0)) ((I'.interpretation.basis .sphere 13 138 3)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
        unfold Raw.claims
        iterate 288 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 2 (11,137) (13,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h289 : KIP126.SpectralSequence.HasDifferential E 2 (11,137) (13,138)
        ((I'.interpretation.basis .sphere 11 137 3)) ((I'.interpretation.basis .sphere 13 138 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
        unfold Raw.claims
        iterate 289 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 2 (11,137) (13,138) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h329 : KIP126.SpectralSequence.HasDifferential E 3 (13,138) (16,140)
        ((I'.interpretation.basis .sphere 13 138 1)) ((I'.interpretation.basis .sphere 16 140 1)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
        unfold Raw.claims
        iterate 329 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change KIP126.SpectralSequence.HasDifferential E 3 (13,138) (16,140) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd

    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
      unfold Raw.degrees
      iterate 209 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 13 138 i.val at he

    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 13 138 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 13 138 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 13 138 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 13 138 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 13 138 4 := he 4

    constructor
    · obtain ⟨_, a, b, ha, hb, hd⟩ := h329
      exact ((isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,138)
        (I'.interpretation.basis .sphere 13 138 1)).mpr ⟨a,ha⟩).2
    · intro x
      let P := boundaries H SphereSpectrum 4 (13,138)
      have hb0 : I'.interpretation.basis .sphere 13 138 0 ∈ P :=
        boundary_of_zero_representative (r:=5) (p:=(13,138))
          (differential_target_later_zero (by change (2:ℤ)≤4; omega)
            (by decide : (4:ℤ)<5) h231)
      have hb2 : I'.interpretation.basis .sphere 13 138 2 ∈ P :=
        boundary_of_zero_representative (r:=5) (p:=(13,138))
          (differential_target_later_zero (by change (2:ℤ)≤4; omega)
            (by decide : (4:ℤ)<5) h232)
      have hb3 : I'.interpretation.basis .sphere 13 138 3 ∈ P :=
        boundary_of_zero_representative (r:=5) (p:=(13,138))
          (differential_target_later_zero (by change (2:ℤ)≤2; omega)
            (by decide : (2:ℤ)<5) h288)
      have hb4 : I'.interpretation.basis .sphere 13 138 4 ∈ P :=
        boundary_of_zero_representative (r:=5) (p:=(13,138))
          (differential_target_later_zero (by change (2:ℤ)≤2; omega)
            (by decide : (2:ℤ)<5) h289)
      have hif (c : F2) {a : Page D' .sphere 13 138} (h : a ∈ P) :
          (if c=0 then 0 else a) ∈ P := by
        split
        · exact P.zero_mem
        · exact h
      let c : Fin 5 → F2 := e x
      have hcoef := congrArg e.symm (middle_expand (e x))
      simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
      change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
      simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
      have hm := P.add_mem (hif (c 0) hb0)
        (P.add_mem (hif (c 2) hb2) (P.add_mem (hif (c 3) hb3) (hif (c 4) hb4)))
      by_cases hc : c 1=0
      · left
        change x ∈ P
        rw [hcoef]
        simpa only [hc,ite_true,zero_add] using hm
      · right
        change x - I'.interpretation.basis .sphere 13 138 1 ∈ P
        rw [hcoef]
        simp only [hc,ite_false]
        convert hm using 1 <;> first | rfl | abel
  have nu9_af12_cycles_boundary (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      cycles H SphereSpectrum 2 (12,137) ≤ boundaries H SphereSpectrum 3 (12,137) := by
    intro x hx
    obtain ⟨a,ha⟩ := (isCycle_iff_represents H SphereSpectrum 3 (by decide) (12,137) x).mp
      ⟨by decide, by simpa using hx⟩
    have hself := middle_rep2 (E:=sequence D' .sphere) (r:=3) (p:=(12,137)) (by decide : (2:ℤ)≤3) ha
    have hd : (sequence D' .sphere).d 2 (12,137) x=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
        hself ⟨a,ha⟩
    exact boundary_of_zero_representative (r:=4) (p:=(12,137)) (nu9_af12_kernel I' x hd)
  have nu9_af12_cycle_quotient_zero (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      Subsingleton (CycleQuotient H SphereSpectrum 2 8 (12,137)) := by
    have hz (x : CycleQuotient H SphereSpectrum 2 8 (12,137)) : x=0 := by
      obtain ⟨x⟩ := x
      exact (NestedQuotient.projection_eq_zero x).mpr
        (boundaries_monotone H SphereSpectrum (12,137) (by decide : (3:ℤ)≤8)
          (nu9_af12_cycles_boundary I' x.property))
    exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
  have nu9_af13_cosets_nine (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      I'.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
      ∀ x : Page D' .sphere 13 138,
        x ∈ boundaries H SphereSpectrum 9 (13,138) ∨
        x - I'.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 9 (13,138) := by
    obtain ⟨hc,h⟩ := nu9_af13_cosets I'
    refine ⟨hc,fun x=>?_⟩
    rcases h x with hx | hx
    · exact Or.inl (boundaries_monotone H SphereSpectrum (13,138) (by decide : (4:ℤ)≤9) hx)
    · exact Or.inr (boundaries_monotone H SphereSpectrum (13,138) (by decide : (4:ℤ)≤9) hx)
  exact ⟨nu9_af12_cycle_quotient_zero I',nu9_af13_cosets_nine I'⟩
end
private theorem nu_ninth_of_fifth_complete
    {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
    (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
    (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
    (SF : Derived.SphereFacts I'.interpretation) (ν : BiHom 3 4 (S_0_0 : Syn))
    (h5 : NuExtension5 D' (I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X)
      (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) ν) :
    NuExtension9 D' (I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X)
      (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) ν := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b) : a = b := by
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
  have nu9_af12_cycle_quotient_zero {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      Subsingleton (CycleQuotient H SphereSpectrum 2 8 (12,137)) := (nu9_error_data I').1
  have nu9_af13_cosets_nine {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      I'.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
      ∀ x : KIP126.Computation.SphereAndCofiber.Page D' .sphere 13 138,
        x ∈ boundaries H SphereSpectrum 9 (13,138) ∨
        x - I'.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 9 (13,138) := (nu9_error_data I').2
  have shift_assoc_inv (coh : BiShiftCoherence Syn)
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
  let weightShiftHom {m w : ℤ} {A : Syn} (k : ℤ) (a : BiHom m w A) :
      BiHom m (w+k) ((SyntheticCategory.biShift (0,k)).obj A) :=
    (biShiftAddIso (m,w) (0,k) (m,w+k) (by ext <;> simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,k)).map a
  have weightShiftHom_weight (D' : AdamsComparison H M' Syn)
      (m w k : ℤ) (A : Syn) (a : BiHom m w A) :
      weightHomotopyMap m (w+k) ((SyntheticCategory.biShift (0,k)).obj A)
        (weightShiftHom k a) ≫ (weightShiftObjectIso A k w).hom =
      weightHomotopyMap m w A a := by
    have ha := shift_assoc_inv D'.shiftCoherence (m,w) (0,k) (0,-(w+k))
      (m,w+k) (0,-w) (m,0)
      (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (S_0_0 : Syn)
    have hsource (m w : ℤ) : weightSourceIso (Syn:=Syn) m w =
        (biShiftAddIso (m,w) (0,-w) (m,0) (by ext <;> simp)).app S_0_0 ≪≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) m).app S_0_0 := by
      apply Iso.ext
      simp only [weightSourceIso,biShiftAddIso,Iso.app_hom,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc]
    have hobject : weightShiftObjectIso A k w =
        (biShiftAddIso (0,k) (0,-(w+k)) (0,-w) (by ext <;> simp)).app A := by
      apply Iso.ext
      simp only [weightShiftObjectIso,biShiftAddIso,Iso.app_hom,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app]
    dsimp only [weightHomotopyMap,weightShiftHom]
    rw [hsource,hsource,hobject]
    simp only [Iso.trans_inv,Iso.app_hom,Iso.app_inv,Functor.map_comp,Category.assoc]
    erw [reassoc_of% ha]
    erw [((biShiftAddIso (0,k) (0,-(w+k)) (0,-w) (by ext <;> simp)).hom.naturality a)]
    change (SyntheticCategory.biShift_compat m).inv.app S_0_0 ≫ _ = _
    erw [Iso.inv_hom_id_app_assoc]
  have canonical_weight_shift_e1
      (S : EInftyWeightShift D'.family)
      (hc : CanonicalWeightShift D'.towerPresentation S)
      (A : Syn) (k s t w : ℤ)
      (z : FamilyInfiniteRepresentative D'.family ((SyntheticCategory.biShift (0,k)).obj A) (s,t,w+k)) :
      ∃ z' : FamilyInfiniteRepresentative D'.family A (s,t,w),
        familyInfiniteRepresentativeE1 (nuCoefficientUnit H.unit D'.nu) D'.towerPresentation A (s,t,w) z' =
          adamsE1Induced (nuCoefficientUnit H.unit D'.nu) (weightShiftObjectIso A k w).hom s t
            (familyInfiniteRepresentativeE1 (nuCoefficientUnit H.unit D'.nu) D'.towerPresentation
              ((SyntheticCategory.biShift (0,k)).obj A) (s,t,w+k) z) ∧
        S.iso A k (s,t) w (((D'.family.obj ((SyntheticCategory.biShift (0,k)).obj A)).sequence.ssData
          (s,t,w+k)).pageπ ⊤ z) = ((D'.family.obj A).sequence.ssData (s,t,w)).pageπ ⊤ z' := by
    obtain ⟨z',hz',he⟩ := hc A k (s,t) w z
    refine ⟨z',?_,he⟩
    let P := D'.towerPresentation
    let Sh := ((D'.family.obj ((SyntheticCategory.biShift (0,k)).obj A)).sequence.ssData (s,t,w+k))
    let U := ((D'.family.obj A).sequence.ssData (s,t,w))
    have raw : (P.forward A w).φ (s,t) ((U.Z ⊤).arrow z') =
        (adamsCycleInduced (nuCoefficientUnit H.unit D'.nu) (weightShiftObjectIso A k w).hom
          2 (by decide) s t) ((P.forward ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).φ (s,t)
            ((Sh.Z ⊤).arrow z)) := by
      rw [hz']
      change ((P.forward ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).φ (s,t) ≫
          ModuleCat.ofHom (adamsCycleInduced (nuCoefficientUnit H.unit D'.nu)
            (weightShiftObjectIso A k w).hom 2 (by decide) s t) ≫ (P.inverse A w).φ (s,t) ≫
            (P.forward A w).φ (s,t)) ((Sh.Z ⊤).arrow z)=_
      rw [P.right_inv]
      erw [Category.comp_id]
      rfl
    have source_square := congrArg (fun f => f.hom z')
      ((P.forward A w).cycleMap_arrow (s,t) ⊤)
    have target_square := congrArg (fun f => f.hom z)
      ((P.forward ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).cycleMap_arrow (s,t) ⊤)
    change (((weightTower (nuCoefficientUnit H.unit D'.nu) A w).ssData (s,t)).Z ⊤).arrow
      ((P.forward A w).cycleMap (s,t) ⊤ z') =
        (P.forward A w).φ (s,t) ((U.Z ⊤).arrow z') at source_square
    change (((weightTower (nuCoefficientUnit H.unit D'.nu)
        ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).ssData (s,t)).Z ⊤).arrow
      ((P.forward ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).cycleMap (s,t) ⊤ z) =
        (P.forward ((SyntheticCategory.biShift (0,k)).obj A) (w+k)).φ (s,t)
          ((Sh.Z ⊤).arrow z) at target_square
    exact (congrArg Subtype.val source_square).trans
      ((congrArg Subtype.val raw).trans
        (congrArg (adamsE1Induced (nuCoefficientUnit H.unit D'.nu)
          (weightShiftObjectIso A k w).hom s t) (congrArg Subtype.val target_square)).symm)
  have canonical_weight_shift_graded
      (S : EInftyWeightShift D'.family)
      (hc : CanonicalWeightShift D'.towerPresentation S)
      (X : SyntheticObject) (k s t w : ℤ)
      (e : ((D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).sequence.ssData (s,t,w)).eInfty)
      (aa : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)).F s (t-s,w)) : ModuleCat.{v} ℤ))
      (he : ((D'.convergence X).identification (s,t,w)).hom e =
        (towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s (t-s,w) aa) :
      ∃ bb : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
          ((SyntheticObject.shift (0,k) X).obj D'.nu D'.hopfAndDetector)).F s (t-s,w+k)) : ModuleCat.{v} ℤ),
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
          ((SyntheticObject.shift (0,k) X).obj D'.nu D'.hopfAndDetector)).F s (t-s,w+k)).arrow bb =
          weightShiftHom k (((towerFiltration (nuCoefficientUnit H.unit D'.nu)
            (X.obj D'.nu D'.hopfAndDetector)).F s (t-s,w)).arrow aa) ∧
        ((D'.convergence (.shift (0,k) X)).identification (s,t,w+k)).hom
          ((S.iso (X.obj D'.nu D'.hopfAndDetector) k (s,t) w).symm e) =
        (towerFiltration (nuCoefficientUnit H.unit D'.nu)
          ((SyntheticObject.shift (0,k) X).obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s (t-s,w+k) bb := by
    let A := X.obj D'.nu D'.hopfAndDetector
    let B := (SyntheticCategory.biShift (0,k)).obj A
    let unit := nuCoefficientUnit H.unit D'.nu
    let F := towerFiltration unit A
    let G := towerFiltration unit B
    let a := (F.F s (t-s,w)).arrow aa
    let b := weightShiftHom k a
    let g := weightShiftObjectIso A k w
    have ham : a ∈ towerFiltrationSubmodule unit A s (t-s,w) := by
      have hh : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy A (t-s,w))) (F.F s (t-s,w)) := ⟨aa,rfl⟩
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply] using hh
    have hat := (D'.convergence_canonical X).1 s (t-s) w a |>.mp ham
    obtain ⟨aT,haT⟩ := hat
    obtain ⟨bT,hbT⟩ := (adamsTowerHomInduced_bijective unit g.hom (t-s) s).2 aT
    have hbproj : weightHomotopyMap (t-s) (w+k) B b =
        inducedMap (adamsTowerMap unit ((SyntheticCategory.biShift (0,-(w+k))).obj B)
          0 s.toNat (Nat.zero_le _)) (t-s) bT := by
      apply (cancel_mono g.hom).1
      change weightHomotopyMap (t-s) (w+k) B b ≫ g.hom =
        (bT ≫ adamsTowerMap unit ((SyntheticCategory.biShift (0,-(w+k))).obj B)
          0 s.toNat (Nat.zero_le _)) ≫ g.hom
      have hnat := adamsTowerInduced_map unit g.hom 0 s.toNat (Nat.zero_le _)
      change adamsTowerInduced unit g.hom s.toNat ≫
        adamsTowerMap unit ((SyntheticCategory.biShift (0,-w)).obj A) 0 s.toNat (Nat.zero_le _) =
        adamsTowerMap unit ((SyntheticCategory.biShift (0,-(w+k))).obj B) 0 s.toNat (Nat.zero_le _) ≫ g.hom at hnat
      change bT ≫ adamsTowerInduced unit g.hom s.toNat = aT at hbT
      change aT ≫ adamsTowerMap unit ((SyntheticCategory.biShift (0,-w)).obj A)
        0 s.toNat (Nat.zero_le _) = weightHomotopyMap (t-s) w A a at haT
      calc
        _ = weightHomotopyMap (t-s) w A a := weightShiftHom_weight D' (t-s) w k A a
        _ = aT ≫ _ := haT.symm
        _ = (bT ≫ adamsTowerInduced unit g.hom s.toNat) ≫ _ := by rw [hbT]
        _ = _ := by rw [Category.assoc,hnat,Category.assoc]
    have hbm : b ∈ towerFiltrationSubmodule unit B s (t-s,w+k) := by
      apply (D'.convergence_canonical (.shift (0,k) X)).1 s (t-s) (w+k) b |>.mpr
      exact ⟨bT,hbproj.symm⟩
    have hbmem : b ∈ (ModuleCat.subobjectModule (syntheticHomotopy B (t-s,w+k))) (G.F s (t-s,w+k)) := by
      simpa only [G,towerFiltration,OrderIso.apply_symm_apply] using hbm
    obtain ⟨bb,hbb⟩ := hbmem
    obtain ⟨z,hz⟩ := exists_weightLiftRepresentative unit D'.towerPresentation B (s,t,w+k) bT
    obtain ⟨z',hz',heq⟩ := canonical_weight_shift_e1 S hc A k s t w z
    have hzsource : familyInfiniteRepresentativeE1 unit D'.towerPresentation A (s,t,w) z' =
        adamsJ unit ((SyntheticCategory.biShift (0,-w)).obj A) s t aT := by
      rw [hz',hz,adamsJ_naturality,hbT]
    have hs := (D'.convergence_canonical X).2 (s,t,w) aT z' hzsource aa haT.symm
    have hez : ((D'.family.obj A).sequence.ssData (s,t,w)).pageπ ⊤ z' = e :=
      (ModuleCat.mono_iff_injective (((D'.convergence X).identification (s,t,w)).hom)).mp
        inferInstance (hs.trans he.symm)
    have hezt : ((D'.family.obj B).sequence.ssData (s,t,w+k)).pageπ ⊤ z =
        (S.iso A k (s,t) w).symm e := by
      apply (S.iso A k (s,t) w).injective
      rw [LinearEquiv.apply_symm_apply,heq,hez]
    refine ⟨bb,hbb,?_⟩
    have hh := (D'.convergence_canonical (.shift (0,k) X)).2 (s,t,w+k) bT z hz bb
    have hbp : weightHomotopyMap (t-s) (w+k) B ((G.F s (t-s,w+k)).arrow bb) =
        inducedMap (adamsTowerMap unit ((SyntheticCategory.biShift (0,-(w+k))).obj B)
          0 s.toNat (Nat.zero_le _)) (t-s) bT := by
      rw [hbb]
      exact hbproj
    have hfinal := hh hbp
    change ((D'.convergence (.shift (0,k) X)).identification (s,t,w+k)).hom
      (((D'.family.obj B).sequence.ssData (s,t,w+k)).pageπ ⊤ z) = _ at hfinal
    rw [hezt] at hfinal
    exact hfinal
  have canonical_weight_shift_map_graded
      (S : EInftyWeightShift D'.family)
      (hc : CanonicalWeightShift D'.towerPresentation S)
      (X Y : SyntheticObject) (k s t w : ℤ)
      (f : (SyntheticObject.shift (0,k) X).obj D'.nu D'.hopfAndDetector ⟶ Y.obj D'.nu D'.hopfAndDetector)
      (e : ((D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).sequence.ssData (s,t,w)).eInfty)
      (aa : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)).F s (t-s,w)) : ModuleCat.{v} ℤ))
      (he : ((D'.convergence X).identification (s,t,w)).hom e =
        (towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s (t-s,w) aa) :
      ∃ bb : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
          (Y.obj D'.nu D'.hopfAndDetector)).F s (t-s,w+k)) : ModuleCat.{v} ℤ),
        ((towerFiltration (nuCoefficientUnit H.unit D'.nu)
          (Y.obj D'.nu D'.hopfAndDetector)).F s (t-s,w+k)).arrow bb =
          weightShiftHom k (((towerFiltration (nuCoefficientUnit H.unit D'.nu)
            (X.obj D'.nu D'.hopfAndDetector)).F s (t-s,w)).arrow aa) ≫ f ∧
        ((D'.convergence Y).identification (s,t,w+k)).hom
          ((D'.family.functor.map f).eInftyMap (s,t,w+k)
            ((S.iso (X.obj D'.nu D'.hopfAndDetector) k (s,t) w).symm e)) =
        (towerFiltration (nuCoefficientUnit H.unit D'.nu)
          (Y.obj D'.nu D'.hopfAndDetector)).toAssociatedGraded s (t-s,w+k) bb := by
    obtain ⟨a',ha',hgr⟩ := canonical_weight_shift_graded S hc X k s t w e aa he
    obtain ⟨c,hca,hce⟩ := D'.comparisonCompatible.convergence_natural (.shift (0,k) X) Y f
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) ((SyntheticObject.shift (0,k) X).obj D'.nu D'.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D'.nu) (Y.obj D'.nu D'.hopfAndDetector)
    let m := (t-s,w+k)
    let i : Tridegree := (s,t,w+k)
    let g := (c.filtration_compat s m).choose
    have hg : g≫(G.F s m).arrow=(F.F s m).arrow≫syntheticHomotopyMap f m := by
      have hh := (c.filtration_compat s m).choose_spec
      change g≫(G.F s m).arrow=(F.F s m).arrow≫c.aMap m at hh
      rw [hca] at hh
      exact hh
    have hcon : c.eMap i ≫ ((D'.convergence Y).identification i).hom =
        ((D'.convergence (.shift (0,k) X)).identification i).hom ≫
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m := by
      have hh := c.iso_compat i
      simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,
        Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
    have hq : F.toAssociatedGraded s m ≫
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m =
        g≫G.toAssociatedGraded s m := cokernel.π_desc _ _ _
    refine ⟨g a',?_,?_⟩
    · have hh := ConcreteCategory.congr_hom hg a'
      change (G.F s m).arrow (g a')=((F.F s m).arrow a')≫f at hh
      change (F.F s m).arrow a'=_ at ha'
      rw [ha'] at hh
      exact hh
    · have hh := ConcreteCategory.congr_hom hcon ((S.iso (X.obj D'.nu D'.hopfAndDetector) k (s,t) w).symm e)
      rw [hce] at hh
      calc
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m)
            (((D'.convergence (.shift (0,k) X)).identification i).hom
              ((S.iso (X.obj D'.nu D'.hopfAndDetector) k (s,t) w).symm e)) := hh
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m)
            (F.toAssociatedGraded s m a') := by rw [hgr]
        _ = G.toAssociatedGraded s m (g a') := ConcreteCategory.congr_hom hq a'
  have nu_fourth_x_detected
      (BHS : KIP126.Literature.AdamsSynthetic.EInftyComparison D')
      (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
      (x : E2 H SphereSpectrum 8 130)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum 5 (8,130))
      (a : BiHom 122 130 (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 5))
      (ha : Detects (D'.convergence (.quotient 5 (.nu .sphere))) (8,130,130)
        (finiteTargetLabel D' .sphere 5 8 130 0 x) a) :
      Detects (D'.convergence (.quotient 9 (.nu .sphere))) (8,130,126)
        (finiteTargetLabel D' .sphere 9 8 130 4 x)
        (weightShiftHom (-4) a ≫ (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)) := by
    obtain ⟨e,he,aa,haa,hgr⟩ := ha
    let f := (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)
    let e' := BHS.weightShift.finiteLambdaMap (D'.quotientTower (D'.nu.functor.obj SphereSpectrum))
      9 4 (by decide) (8,130) 130 e
    have hs := (BHS.labels.1 .sphere 5 (by decide) (8,130) 0 (by decide) ⟨x,hx⟩ e).mp he
    have hh := BHS.maps.lambda_finite SphereSpectrum 9 4 (by decide) (8,130) 130 (by norm_num) e
    erw [hs] at hh
    have hre : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 9) 2 (8,130,126)
        (finiteTargetLabel D' .sphere 9 8 130 4 x) e' := by
      apply (BHS.labels.1 .sphere 9 (by decide) (8,130) 4 (by decide) ⟨x,hx⟩ e').mpr
      exact hh
    obtain ⟨bb,hbb,hbg⟩ := canonical_weight_shift_map_graded BHS.weightShift hc
      (.quotient 5 (.nu .sphere)) (.quotient 9 (.nu .sphere)) (-4) 8 130 130 f e aa hgr
    refine ⟨e',hre,bb,?_,hbg⟩
    exact hbb.trans (congrArg (fun z => weightShiftHom (-4) z ≫ f) haa)
  have nu_fourth_y_detected
      (BHS : KIP126.Literature.AdamsSynthetic.EInftyComparison D')
      (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
      (x : E2 H SphereSpectrum 11 136)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum 3 (11,136))
      (a : BiHom 125 134 (XModLambdaN (D'.nu.functor.obj SphereSpectrum) 5))
      (ha : Detects (D'.convergence (.quotient 5 (.nu .sphere))) (11,136,134)
        (finiteTargetLabel D' .sphere 5 11 136 2 x) a) :
      Detects (D'.convergence (.quotient 9 (.nu .sphere))) (11,136,130)
        (finiteTargetLabel D' .sphere 9 11 136 6 x)
        (weightShiftHom (-4) a ≫ (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)) := by
    obtain ⟨e,he,aa,haa,hgr⟩ := ha
    let f := (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)
    let e' := BHS.weightShift.finiteLambdaMap (D'.quotientTower (D'.nu.functor.obj SphereSpectrum))
      9 4 (by decide) (11,136) 134 e
    have hs := (BHS.labels.1 .sphere 5 (by decide) (11,136) 2 (by decide) ⟨x,hx⟩ e).mp he
    have hh := BHS.maps.lambda_finite SphereSpectrum 9 4 (by decide) (11,136) 134 (by norm_num) e
    erw [hs] at hh
    have hre : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum 9) 2 (11,136,130)
        (finiteTargetLabel D' .sphere 9 11 136 6 x) e' := by
      apply (BHS.labels.1 .sphere 9 (by decide) (11,136) 6 (by decide) ⟨x,hx⟩ e').mpr
      exact hh
    obtain ⟨bb,hbb,hbg⟩ := canonical_weight_shift_map_graded BHS.weightShift hc
      (.quotient 5 (.nu .sphere)) (.quotient 9 (.nu .sphere)) (-4) 11 136 134 f e aa hgr
    refine ⟨e',hre,bb,?_,hbg⟩
    exact hbb.trans (congrArg (fun z => weightShiftHom (-4) z ≫ f) haa)
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
  have sphere_quotient_label_from_nu (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) = D'.quotientLabel q s t k x := by
    rw [←sphere_quotient_label_to_nu q k s t x]
    have hcomp := ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.map D'.nu.unitIso.inv q) (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k))
      (D'.quotientLabel q s t k x)
    have hgf : XModLambdaN.map D'.nu.unitIso.inv q ≫ XModLambdaN.map D'.nu.unitIso.hom q = 𝟙 _ := by
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hid : familyPageMap D'.family (𝟙 (XModLambdaN (S_0_0 : Syn) q)) 2 (s,t,t-k) = 𝟙 _ := by
      rw [family_map_data,CategoryTheory.Functor.map_id]
      exact SSDataMorphism.pageMap_id
        (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-k) (↑(2-2:ℤ).toNat)
    exact hcomp.trans (by rw [hgf]; erw [hid]; rfl)
  have fourth_sphere_transport (a : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5)) :
      (weightShiftHom (-4) (a≫XModLambdaN.map D'.nu.unitIso.inv 5) ≫
        (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)) ≫
        XModLambdaN.map D'.nu.unitIso.hom 9 =
      weightShiftHom (-4) a ≫ (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide) := by
    have hn := (D'.comparisonCompatible.quotient_naturality D'.nu.unitIso.inv).lambda_naturality
      (i:=4) (j:=9) (by decide) (by decide)
    have hg : XModLambdaN.map D'.nu.unitIso.inv 9 ≫ XModLambdaN.map D'.nu.unitIso.hom 9 = 𝟙 _ := by
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    change (SyntheticCategory.biShift (0,-4)).map (XModLambdaN.map D'.nu.unitIso.inv 5) ≫
      (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide) =
      (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide) ≫
        XModLambdaN.map D'.nu.unitIso.inv 9 at hn
    dsimp only [weightShiftHom]
    simp only [Functor.map_comp,Category.assoc]
    erw [reassoc_of% hn,hg,Category.comp_id]
  have fourth_sphere_transport_x (a : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 5)) :
      (weightShiftHom (-4) (a≫XModLambdaN.map D'.nu.unitIso.inv 5) ≫
        (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide)) ≫
        XModLambdaN.map D'.nu.unitIso.hom 9 =
      weightShiftHom (-4) a ≫ (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide) := by
    have hn := (D'.comparisonCompatible.quotient_naturality D'.nu.unitIso.inv).lambda_naturality
      (i:=4) (j:=9) (by decide) (by decide)
    have hg : XModLambdaN.map D'.nu.unitIso.inv 9 ≫ XModLambdaN.map D'.nu.unitIso.hom 9 = 𝟙 _ := by
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    change (SyntheticCategory.biShift (0,-4)).map (XModLambdaN.map D'.nu.unitIso.inv 5) ≫
      (D'.quotientTower (D'.nu.functor.obj SphereSpectrum)).lambdaInclusion 4 9 (by decide) =
      (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide) ≫
        XModLambdaN.map D'.nu.unitIso.inv 9 at hn
    dsimp only [weightShiftHom]
    simp only [Functor.map_comp,Category.assoc]
    erw [reassoc_of% hn,hg,Category.comp_id]
  have sphere_fourth_x_detected
      (BHS : KIP126.Literature.AdamsSynthetic.EInftyComparison D')
      (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
      (x : E2 H SphereSpectrum 8 130)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum 5 (8,130))
      (a : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 5))
      (ha : Detects (D'.quotientConvergence 5 (by decide)) (8,130,130)
        (D'.quotientLabel 5 8 130 0 x) a) :
      Detects (D'.quotientConvergence 9 (by decide)) (8,130,126)
        (D'.quotientLabel 9 8 130 4 x)
        (weightShiftHom (-4) a ≫ (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide)) := by
    have hn := detected_map (.quotient 5 .sphere) (.quotient 5 (.nu .sphere))
      (XModLambdaN.map D'.nu.unitIso.inv 5) (8,130,130) _ a ha
    erw [sphere_quotient_label_to_nu 5 0 8 130 x] at hn
    have hp := nu_fourth_x_detected BHS hc x hx (a≫XModLambdaN.map D'.nu.unitIso.inv 5) hn
    have hs := detected_map (.quotient 9 (.nu .sphere)) (.quotient 9 .sphere)
      (XModLambdaN.map D'.nu.unitIso.hom 9) (8,130,126) _ _ hp
    erw [sphere_quotient_label_from_nu 9 4 8 130 x,fourth_sphere_transport_x] at hs
    exact hs
  have sphere_fourth_y_detected
      (BHS : KIP126.Literature.AdamsSynthetic.EInftyComparison D')
      (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
      (x : E2 H SphereSpectrum 11 136)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum 3 (11,136))
      (a : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5))
      (ha : Detects (D'.quotientConvergence 5 (by decide)) (11,136,134)
        (D'.quotientLabel 5 11 136 2 x) a) :
      Detects (D'.quotientConvergence 9 (by decide)) (11,136,130)
        (D'.quotientLabel 9 11 136 6 x)
        (weightShiftHom (-4) a ≫ (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide)) := by
    have hn := detected_map (.quotient 5 .sphere) (.quotient 5 (.nu .sphere))
      (XModLambdaN.map D'.nu.unitIso.inv 5) (11,136,134) _ a ha
    erw [sphere_quotient_label_to_nu 5 2 11 136 x] at hn
    have hp := nu_fourth_y_detected BHS hc x hx (a≫XModLambdaN.map D'.nu.unitIso.inv 5) hn
    have hs := detected_map (.quotient 9 (.nu .sphere)) (.quotient 9 .sphere)
      (XModLambdaN.map D'.nu.unitIso.hom 9) (11,136,130) _ _ hp
    erw [sphere_quotient_label_from_nu 9 6 11 136 x,fourth_sphere_transport] at hs
    exact hs
  let sphere_unit (D' : AdamsComparison H M' Syn) : BiHom 0 0 (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.hom.app _
  let sphere_unit_label (D' : AdamsComparison H M' Syn) : E2 H SphereSpectrum 0 0 :=
    D'.sphereFirstQuotient 0 0 (quotientClass 1 (sphere_unit D'))
  have lambda_sphere_unit (D' : AdamsComparison H M' Syn) :
      lambdaMultiply 1 (sphere_unit D') = SyntheticCategory.lam.app (S_0_0 : Syn) := by
    have hu := D'.shiftCoherence.left_unit (0,-1) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold lambdaMultiply sphere_unit
    simp only [eqToHom_refl,Category.id_comp]
    erw [←lambdaPow_naturality 1 (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn))]
    erw [←hu,Iso.inv_hom_id_app_assoc]
    exact lambdaPow_one D'.shiftCoherence _
  have sphere_lambda_action (D' : AdamsComparison H M' Syn) {A : Syn}
      (a : BiHom 125 131 A) :
      sphereAction (lambdaMultiply 1 (sphere_unit D')) a = lambdaMultiply 1 a := by
    rw [lambda_sphere_unit D']
    have hc := D'.shiftCoherence.lambda_comm (125,131) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
      eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp]
    erw [lambdaPow_one D'.shiftCoherence, hc]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc]
    rfl
  have sphere_unit_action_136 (D' : AdamsComparison H M' Syn) {A : Syn}
      (a : BiHom 125 136 A) : sphereAction (sphere_unit D') a = a := by
    have hu := D'.shiftCoherence.left_unit (125,136) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold sphereAction sphere_unit
    erw [←hu,Iso.inv_hom_id_app_assoc]
  have sphere_unit_label_product_136
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 11 136) :
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D') y = y := by
    letI := A.syntheticSymmetric
    let b := (D'.sphereFirstQuotient 11 136).symm y
    have hb : D'.sphereFirstQuotient 11 136 b = y := (D'.sphereFirstQuotient 11 136).apply_symm_apply y
    have h := ab.first_quotient 0 0 11 136 (quotientClass 1 (sphere_unit D')) b
    change D'.sphereFirstQuotient 11 136
      (KIP126.Literature.AdamsSynthetic.algebraProduct (A.quotients.algebra 1 (by decide))
        (quotientClass 1 (sphere_unit D')) b) = _ at h
    rw [qb.sphere_action 1 (by decide) 0 0 125 136,sphere_unit_action_136 D'] at h
    change D'.sphereFirstQuotient 11 136 b =
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D')
        (D'.sphereFirstQuotient 11 136 b) at h
    rw [hb] at h
    exact h.symm
  have lambda_one_finite_detected_136
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 11 136)
      (a : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : Detects (D'.quotientConvergence 9 (by decide)) (11,136,131)
        (D'.quotientLabel 9 11 136 5 y) a) :
      Detects (D'.quotientConvergence 9 (by decide)) (11,136,130)
        (D'.quotientLabel 9 11 136 6 y) (lambdaMultiply 1 a) := by
    have hu := D'.comparisonCompatible.homotopy_lambda 0 0 1 (sphere_unit D')
    have hh := ab.finite_action 9 (by decide) 0 0 11 136 1 5
      (sphere_unit_label D') y (lambdaMultiply 1 (sphere_unit D')) a hu ha
    change Detects (D'.quotientConvergence 9 (by decide)) (11,136,130)
      (D'.quotientLabel 9 11 136 6
        (Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D') y))
      (sphereAction (lambdaMultiply 1 (sphere_unit D')) a) at hh
    rw [sphere_unit_label_product_136 A qb ab y,sphere_lambda_action D'] at hh
    exact hh
  have sphere_unit_action_138 (D' : AdamsComparison H M' Syn) {A : Syn}
      (a : BiHom 125 138 A) : sphereAction (sphere_unit D') a = a := by
    have hu := D'.shiftCoherence.left_unit (125,138) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold sphereAction sphere_unit
    erw [←hu,Iso.inv_hom_id_app_assoc]
  have sphere_unit_label_product_138
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 13 138) :
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=13) (t':=138) (sphere_unit_label D') y = y := by
    letI := A.syntheticSymmetric
    let b := (D'.sphereFirstQuotient 13 138).symm y
    have hb : D'.sphereFirstQuotient 13 138 b = y := (D'.sphereFirstQuotient 13 138).apply_symm_apply y
    have h := ab.first_quotient 0 0 13 138 (quotientClass 1 (sphere_unit D')) b
    change D'.sphereFirstQuotient 13 138
      (KIP126.Literature.AdamsSynthetic.algebraProduct (A.quotients.algebra 1 (by decide))
        (quotientClass 1 (sphere_unit D')) b) = _ at h
    rw [qb.sphere_action 1 (by decide) 0 0 125 138,sphere_unit_action_138 D'] at h
    change D'.sphereFirstQuotient 13 138 b =
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=13) (t':=138) (sphere_unit_label D')
        (D'.sphereFirstQuotient 13 138 b) at h
    rw [hb] at h
    exact h.symm
  have lambda_one_finite_detected_138
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 13 138)
      (a : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : Detects (D'.quotientConvergence 9 (by decide)) (13,138,131)
        (D'.quotientLabel 9 13 138 7 y) a) :
      Detects (D'.quotientConvergence 9 (by decide)) (13,138,130)
        (D'.quotientLabel 9 13 138 8 y) (lambdaMultiply 1 a) := by
    have hu := D'.comparisonCompatible.homotopy_lambda 0 0 1 (sphere_unit D')
    have hh := ab.finite_action 9 (by decide) 0 0 13 138 1 7
      (sphere_unit_label D') y (lambdaMultiply 1 (sphere_unit D')) a hu ha
    change Detects (D'.quotientConvergence 9 (by decide)) (13,138,130)
      (D'.quotientLabel 9 13 138 8
        (Sphere.Internal.product H M' (s:=0) (t:=0) (s':=13) (t':=138) (sphere_unit_label D') y))
      (sphereAction (lambdaMultiply 1 (sphere_unit D')) a) at hh
    rw [sphere_unit_label_product_138 A qb ab y,sphere_lambda_action D'] at hh
    exact hh
  have finite_detection_peel
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
  have finite_sphere_frame
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
        rw [←sphere_quotient_label_to_nu q k s t c.val]
        calc
          _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k c.val) :=
            ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
          _ = D'.quotientLabel q s t k c.val := by
            rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
            exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
              (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
              (s,t,t-k) ↑(2-2:ℤ).toNat) _
      have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
      rw [hl,heq] at h
      exact h
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
  have sphere_finite_detection_exists_weak
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
      (x : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t)) :
      ∃ a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q),
        Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x.val) a := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k) (by constructor <;> omega)
    let en := P.symm (NestedQuotient.projection _ _ x)
    have hn := (BHS.labels.1 .sphere q hq (s,t) k hk x en).mpr (P.apply_symm_apply _)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let e := (D'.family.functor.map f).eInftyMap (s,t,t-k) en
    have he : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k x.val) e := by
      have hh := family_infinity_representative_map f (s,t,t-k) _ _ hn
      erw [sphere_quotient_label_from_nu q k s t x.val] at hh
      exact hh
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) q)
    haveI : Epi (F.toAssociatedGraded s (t-s,t-k)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t-k))).mp
      inferInstance (((D'.quotientConvergence q hq).identification (s,t,t-k)).hom e)
    exact ⟨(F.F s (t-s,t-k)).arrow a,e,he,a,rfl,ha.symm⟩
  have detects_zero_of_filtration
      (O : SyntheticObject) (s t w : ℤ)
      (a : BiHom (t-s) w (O.obj D'.nu D'.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (s+1) a) :
      Detects (D'.convergence O) (s,t,w) 0 a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (O.obj D'.nu D'.hopfAndDetector)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (O.obj D'.nu D'.hopfAndDetector) (t-s,w)))
        (F.F (s+1) (t-s,w)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let f := Subobject.ofLE (F.F (s+1) (t-s,w)) (F.F s (t-s,w)) (F.mono s (t-s,w))
    refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,f a',?_,?_⟩
    · exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow (F.mono s (t-s,w))) a').trans ha'
    · rw [map_zero]
      change 0=(f≫F.toAssociatedGraded s (t-s,w)) a'
      change 0=(f≫cokernel.π f) a'
      rw [cokernel.condition]
      rfl
  have detects_filtration
      (O : SyntheticObject) (i : Tridegree)
      (x : (D'.family.obj (O.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (O.obj D'.nu D'.hopfAndDetector))
      (ha : Detects (D'.convergence O) i x a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a := by
    obtain ⟨e,he,a',ha',hgr⟩ := ha
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (O.obj D'.nu D'.hopfAndDetector)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (O.obj D'.nu D'.hopfAndDetector)
        (i.2.1-i.1,i.2.2))) (F.F i.1 (i.2.1-i.1,i.2.2)) := ⟨a',ha'⟩
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ham
  have nu_nine_af12_gap {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (a : BiHom 125 130 (XModLambdaN (S_0_0 : Syn) 9)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 a := by
    apply (D'.quotientConvergence 9 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      12 13 125 130 (by decide)
    intro j hj hj'
    have : j=12 := by omega
    subst j
    exact finite_sphere_zero_of_classical_quotient BHS 9 (by decide) 12 137 130 (by norm_num)
      (nu9_af12_cycle_quotient_zero I')
  have nu_nine_af13_frame {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') :
      ∀ e : ((D'.family.quotient (S_0_0 : Syn) 9).sequence.ssData (13,138,130)).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) 9) 2 (13,138,130)
          (D'.quotientLabel 9 13 138 8 (I'.interpretation.basis .sphere 13 138 1)) e := by
    have hc := (nu9_af13_cosets_nine I').1
    let x : PageRepresentatives.cycles H SphereSpectrum ((9:ℤ)-138+(138-(8:ℕ))) (13,138) :=
      ⟨I'.interpretation.basis .sphere 13 138 1,
        PageRepresentatives.cycles_antitone H SphereSpectrum (13,138) (by decide : (1:ℤ)≤2) hc⟩
    apply finite_sphere_frame BHS 9 8 (by decide) (by decide) 13 138 x
    rintro ⟨y⟩
    rcases (nu9_af13_cosets_nine I').2 y.val with hy|hy
    · exact Or.inl ((NestedQuotient.projection_eq_zero y).mpr hy)
    · right
      apply sub_eq_zero.mp
      change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x = 0
      exact (map_sub (NestedQuotient.projection _ _) y x).symm.trans
        ((NestedQuotient.projection_eq_zero (y-x)).mpr hy)
  let fourth_push {m w : ℤ} {X Y : Syn}
      (f : (SyntheticCategory.biShift (0,-4)).obj X ⟶ Y) (a : BiHom m w X) :
      BiHom m (w-4) Y :=
    eqToHom (by congr 1; simp) ≫
      (SyntheticCategory.biShift_comp (m,w) (0,-4)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-4)).map a ≫ f
  have nu_fourth_push (D' : AdamsComparison H M' Syn) {X Y : Syn}
      (f : (SyntheticCategory.biShift (0,-4)).obj X ⟶ Y)
      (ν : BiHom 3 4 (S_0_0 : Syn)) (x : BiHom 122 130 X) :
      sphereAction ν (fourth_push f x) = fourth_push f (sphereAction ν x) := by
    have ha := shift_assoc_inv D'.shiftCoherence (3,4) (122,130) (0,-4)
      (125,134) (122,126) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    simp only [fourth_push, eqToHom_refl, Category.id_comp]
    change
      (SyntheticCategory.biShift_comp (3,4) (122,126)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (122,126)).map ν ≫
        ((SyntheticCategory.biShift_comp (122,130) (0,-4)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (0,-4)).map x ≫ f) =
      (SyntheticCategory.biShift_comp (125,134) (0,-4)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-4)).map
          ((SyntheticCategory.biShift_comp (3,4) (122,130)).inv.app (S_0_0 : Syn) ≫
            (SyntheticCategory.biShift (122,130)).map ν ≫ x) ≫ f
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% ((SyntheticCategory.biShift_comp (122,130) (0,-4)).inv.naturality ν)]
    erw [← reassoc_of% ha]
  have nu5_push_relation (D' : AdamsComparison H M' Syn)
      (ν : BiHom 3 4 (S_0_0 : Syn))
      (x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 5))
      (y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5))
      (h : sphereAction ν x = y) :
      sphereAction ν
        (fourth_push ((D'.quotientTower (S_0_0 : Syn)).triangle
          (i := 4) (j := 9) (by decide) (by decide)).lambdaMap x) =
      fourth_push ((D'.quotientTower (S_0_0 : Syn)).triangle
        (i := 4) (j := 9) (by decide) (by decide)).lambdaMap y := by
    rw [nu_fourth_push D', h]
    rfl
  have nu_ninth_of_fifth_weak
      {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (hc : CanonicalWeightShift D'.towerPresentation BHS.weightShift)
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (SF : Derived.SphereFacts I'.interpretation) (ν : BiHom 3 4 (S_0_0 : Syn))
      (h5 : NuExtension5 D' (I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X)
        (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) ν) :
      ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : Syn) 9))
        (y : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9)),
        Detects (D'.quotientConvergence 9 (by decide)) (8,130,126)
          (D'.quotientLabel 9 8 130 4 (I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X)) x ∧
        Detects (D'.quotientConvergence 9 (by decide)) (11,136,131)
          (D'.quotientLabel 9 11 136 5 (I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)) y ∧
        sphereAction ν x = lambdaMultiply 1 y := by
    let X := I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X
    let Y := I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y
    obtain ⟨x5,y5,hx5,hy5,hxy⟩ := h5
    have hX : X ∈ cycles H SphereSpectrum 5 (8,130) := by
      obtain ⟨x,hx,hxn⟩ := SF.x_to_e6
      exact ((isCycle_iff_represents H SphereSpectrum 6 (by decide) (8,130) X).mpr ⟨x,hx⟩).2
    have hY : Y ∈ cycles H SphereSpectrum 4 (11,136) := by
      obtain ⟨y,hy,hyn⟩ := SF.y_to_e5
      exact ((isCycle_iff_represents H SphereSpectrum 5 (by decide) (11,136) Y).mpr ⟨y,hy⟩).2
    let f := (D'.quotientTower (S_0_0 : Syn)).lambdaInclusion 4 9 (by decide)
    let x9 : BiHom 122 126 (XModLambdaN (S_0_0 : Syn) 9) := weightShiftHom (-4) x5 ≫ f
    let yp : BiHom 125 130 (XModLambdaN (S_0_0 : Syn) 9) := weightShiftHom (-4) y5 ≫ f
    have hx9 := sphere_fourth_x_detected BHS hc X hX x5 hx5.1
    have hyp := sphere_fourth_y_detected BHS hc Y
      (cycles_antitone H SphereSpectrum (11,136) (by decide : (3:ℤ)≤4) hY) y5 hy5.1
    obtain ⟨y0,hy⟩ := sphere_finite_detection_exists_weak BHS 9 5 (by decide) (by decide) 11 136 ⟨Y,hY⟩
    let y : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9) := y0
    let ly : BiHom 125 130 (XModLambdaN (S_0_0 : Syn) 9) := lambdaMultiply 1 y
    have hly := lambda_one_finite_detected_136 A qb ab Y y hy
    have herr12 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 (yp-ly) :=
      detects_sub_filtration (D'.quotientConvergence 9 (by decide)) (11,136,130) hyp hly
    have herr13 := (nu_nine_af12_gap I' BHS (yp-ly)).mp herr12
    have hb1 := (nu9_af13_cosets_nine I').1
    obtain ⟨c0,hc⟩ := sphere_finite_detection_exists_weak BHS 9 7 (by decide) (by decide) 13 138
      ⟨I'.interpretation.basis .sphere 13 138 1,hb1⟩
    let c : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9) := c0
    let lc : BiHom 125 130 (XModLambdaN (S_0_0 : Syn) 9) := lambdaMultiply 1 c
    have hlc := lambda_one_finite_detected_138 A qb ab (I'.interpretation.basis .sphere 13 138 1) c hc
    obtain ⟨b,hb⟩ := finite_detection_peel 9 (by decide) (13,138,130)
      (D'.quotientLabel 9 13 138 8 (I'.interpretation.basis .sphere 13 138 1))
      (nu_nine_af13_frame I' BHS) (lc) hlc (yp-ly) herr13
    have hz := sphere_quotient_high_filtration_zero BHS 9 (by decide) 125 130 14 (by decide)
      ((yp-ly)-(if b then lc else 0)) hb
    let y9 : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9) := y+(if b then c else 0)
    have heq : yp=lambdaMultiply 1 y9 := by
      have hh := sub_eq_zero.mp hz
      change yp-ly=(if b then lc else 0) at hh
      have hyadd : lambdaMultiply 1 y9=ly+(if b then lc else 0) := by
        cases b <;> simp only [y9,ly,lc,lambdaMultiply,Bool.false_eq_true,↓reduceIte,
          add_zero,Preadditive.comp_add]
      rw [hyadd]
      exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
    have hc13 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 c :=
      detects_filtration (.quotient 9 .sphere) (13,138,131) _ c hc
    have hc12 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 c :=
      towerFiltrationSubmodule_antitone _ _ (125,131) (by decide : (12:ℤ)≤13) hc13
    have hcz := detects_zero_of_filtration (.quotient 9 .sphere) 11 136 131 c hc12
    have hy9 : Detects (D'.quotientConvergence 9 (by decide)) (11,136,131)
        (D'.quotientLabel 9 11 136 5 Y) y9 := by
      cases b
      · dsimp only [y9]
        simp only [Bool.false_eq_true,↓reduceIte,add_zero]
        exact hy
      · simpa only [y9,↓reduceIte,add_zero] using
          detects_add (D'.quotientConvergence 9 (by decide)) (11,136,131) hy hcz
    refine ⟨x9,y9,hx9,hy9,?_⟩
    have hpush := nu5_push_relation D' ν x5 y5 hxy
    have hs : sphereAction ν x9=yp := by
      simpa only [x9,yp,f,weightShiftHom,fourth_push,FiniteLambdaQuotientTower.lambdaInclusion,
        dif_neg (by decide : ¬(4:ℕ)=0),biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,
        eqToIso.inv,eqToHom_app,eqToHom_refl,Category.id_comp,Category.assoc] using hpush
    exact hs.trans heq
  have sphere_finite_detection_nonzero
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
      (hn : x∉boundaries H SphereSpectrum (1+t-(t-k)) (s,t))
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
      (ha : Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) a) :
      DetectsNonzero (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) a := by
    refine ⟨ha,?_⟩
    obtain ⟨e,he,aa,haa,hgr⟩ := ha
    refine ⟨e,he,?_⟩
    intro he0
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have henu := family_infinity_representative_map g (s,t,t-k) _ _ he
    change HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-k)
      (familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k x)) ((D'.family.functor.map g).eInftyMap (s,t,t-k) e) at henu
    rw [sphere_quotient_label_to_nu q k s t x,he0,map_zero] at henu
    have hh := (BHS.labels.1 .sphere q hq (s,t) k hk ⟨x,hx⟩ 0).mp henu
    rw [map_zero] at hh
    exact hn ((NestedQuotient.projection_eq_zero ⟨x,hx⟩).mp hh.symm)
  obtain ⟨x,y,hx,hy,hxy⟩ := nu_ninth_of_fifth_weak I' BHS hc A qb ab SF ν h5
  let X := I'.interpretation.sphere 8 130 KIP126.Computation.Near126.X
  let Y := I'.interpretation.sphere 11 136 KIP126.Computation.Near126.Y
  obtain ⟨x6,hx6,hx6n⟩ := SF.x_to_e6
  obtain ⟨y5,hy5,hy5n⟩ := SF.y_to_e5
  have hX : X ∈ cycles H SphereSpectrum 5 (8,130) :=
    ((isCycle_iff_represents H SphereSpectrum 6 (by decide) (8,130) X).mpr ⟨x6,hx6⟩).2
  have hY : Y ∈ cycles H SphereSpectrum 4 (11,136) :=
    ((isCycle_iff_represents H SphereSpectrum 5 (by decide) (11,136) Y).mpr ⟨y5,hy5⟩).2
  have hXn : X≠0 := by
    intro hh
    change RepresentsOnPage (sequence D' .sphere) 6 (8,130) X x6 at hx6
    rw [hh] at hx6
    exact hx6n (represents_unique hx6 (RepresentsOnPage.zero (by decide)))
  have hYn : Y≠0 := by
    intro hh
    change RepresentsOnPage (sequence D' .sphere) 5 (11,136) Y y5 at hy5
    rw [hh] at hy5
    exact hy5n (represents_unique hy5 (RepresentsOnPage.zero (by decide)))
  have hXb : X∉boundaries H SphereSpectrum 5 (8,130) :=
    nu9_not_boundary SphereSpectrum (8,130) X hXn 5 (by decide)
      ⟨by decide, by decide, fun r hr _ => SF.x_not_hit.not_hit hr⟩
  have hYb : Y∉boundaries H SphereSpectrum 6 (11,136) :=
    nu9_not_boundary SphereSpectrum (11,136) Y hYn 6 (by decide)
      SF.y_not_hit_through_six
  refine ⟨x,y,?_,?_,hxy⟩
  · exact sphere_finite_detection_nonzero BHS 9 4 (by decide) (by decide) 8 130 X hX hXb x hx
  · exact sphere_finite_detection_nonzero BHS 9 5 (by decide) (by decide) 11 136 Y hY hYb y hy

end
end NuNinthProof


/-- Lift specified Q5 representatives to the required Q9 relation using the
actual lambda^4 map and the existing filtration correction argument. -/
theorem nu_extension_lifts_from_fifth_to_ninth_quotient
    (h5 : NuExtension5 D eX eY h2) : NuExtension9 D eX eY h2 := by
  have hc : CanonicalWeightShift adamsComparison.towerPresentation
      literatureTheorems.synthetic.eInfty.weightShift := by
    change CanonicalWeightShift
      KIP126.Classical.Adams.standardAdamsComparison.towerPresentation
      KIP126.Def.standardEInftyWeightShift
    exact Classical.choose_spec
      (canonicalWeightShift_exists
        KIP126.Classical.Adams.standardAdamsComparison.towerPresentation)
  exact nu_ninth_of_fifth_complete computationTheorems
    literatureTheorems.synthetic.eInfty hc
    literature.sources.sourceComparisons.algebra
    literature.sources.sourceComparisons.quotientCompatibility
    literature.sources.sourceComparisons.algebraDetectionCompatibility
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)
    h2 h5

/-- Lemma 7.20 (`lem:nuext125`): the ν-extension in S⁰,⁰/λ⁹, obtained
from the λ⁴ map on the shifted fifth quotient. The source class needs
only nonzero survival to E₆ and exclusion of incoming differentials;
classical permanence of the source or target is not assumed. -/
theorem lemma_7_20_nu_extension : NuExtension9 D eX eY h2 := by
  exact nu_extension_lifts_from_fifth_to_ninth_quotient nu_extension_lifts_to_fifth_quotient

end
end KIP126.Main.SectionSeven
