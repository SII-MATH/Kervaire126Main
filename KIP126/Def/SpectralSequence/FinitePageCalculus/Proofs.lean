module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs
public import KIP126.Def.Algebra.Coefficients.Data

@[expose] public section

/-! Generic representative and finite-page generation lemmas for internal
spectral sequences. These use the specified cycle and boundary subobjects;
the statements apply to any spectral sequence of modules. -/
namespace KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.SpectralSequence
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

theorem represents_unique
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a b : E.Page r p}
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


theorem represents_d_zero_of_later
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
    {a : E.Page r p} (ha : RepresentsOnPage E r p x a)
    (ht : ReachesPage E t p x) : E.d r p a = 0 := by
  obtain ⟨b, ht2, z, hz, _⟩ := ht
  let D := E.ssData p
  let nt : WithTop ℕ := ↑(t-E.r₀).toNat
  let nr : WithTop ℕ := ↑(r-E.r₀).toNat
  let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
  have hrs : nr ≤ ns := by
    dsimp only [nr, ns]
    exact_mod_cast (show (r-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
  have hst : ns ≤ nt := by
    dsimp only [ns, nt]
    exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z nt) (D.Z nr) (D.Z_anti (hrs.trans hst))) z
  have hrep : RepresentsOnPage E r p x (D.pageπ nr zr) := by
    refine ⟨ha.1, zr, ?_, rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  rw [represents_unique ha hrep]
  change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
  rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
  refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z, ?_⟩
  change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
    ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  rfl


theorem next_projection_zero_iff_incoming
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ)) :
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


theorem page_generated_from_representatives
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r)
    {N : ℕ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ KIP126.Algebra.F2))
    (v : Fin N → E.Page r p)
    (hv : ∀ i, RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) (v i))
    (a : E.Page r p) :
    ∃ c : Fin N → KIP126.Algebra.F2, a = ∑ i, if c i = 0 then 0 else v i := by
  classical
  have hadd {x y : E.Page 2 p} {xr yr : E.Page r p}
      (hx : RepresentsOnPage E r p x xr) (hy : RepresentsOnPage E r p y yr) :
      RepresentsOnPage E r p (x+y) (xr+yr) := by
    obtain ⟨hr, zx, hx, hxr⟩ := hx
    obtain ⟨_, zy, hy, hyr⟩ := hy
    exact ⟨hr, zx+zy, by rw [map_add,hx,hy], by rw [map_add,hxr,hyr]⟩
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  haveI : Epi (D.pageπ n) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ n)).mp inferInstance a
  let x : E.Page 2 p := (Subobject.ofLE _ _ (D.Z_anti (by
    dsimp only [n]
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega))) ≫ D.pageπ _) z
  have hxa : RepresentsOnPage E r p x a := ⟨hr,z,rfl,hz⟩
  let c : Fin N → KIP126.Algebra.F2 := e x
  have hsum (s : Finset (Fin N)) :
      RepresentsOnPage E r p
        (∑ i ∈ s, if c i = 0 then 0 else e.symm (Finsupp.single i 1))
        (∑ i ∈ s, if c i = 0 then 0 else v i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (RepresentsOnPage.zero (E := E) (p := p) hr)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      apply hadd _ ih
      by_cases hc : c i = 0
      · simpa only [hc,ite_true] using (RepresentsOnPage.zero (E := E) (p := p) hr)
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
  refine ⟨c, represents_unique (E:=E) (r:=r) (p:=p) (x:=x) hxa ?_⟩
  have hh := hsum Finset.univ
  simpa only [hx] using hh


theorem represents_before
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {xt : E.Page t p}
    (hr : 2 ≤ r) (hrt : r ≤ t) (ht : RepresentsOnPage E t p x xt) :
    ∃ xr, RepresentsOnPage E r p x xr := by
  obtain ⟨_, z, hz, _⟩ := ht
  let D := E.ssData p
  have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(t-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z ↑(t-E.r₀).toNat) (D.Z ↑(r-E.r₀).toNat) (D.Z_anti hrt')) z
  refine ⟨D.pageπ _ zr, hr, zr, ?_, rfl⟩
  dsimp only [zr]
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz


theorem next_page_two_of_kernel
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)) (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (v : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ))
    (hcases : ∀ a : E.Page r p, E.d r p a = 0 → a = 0 ∨
      a = (Subobject.ofLE _ _ ((E.ssData p).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData p).pageπ ↑(r-E.r₀).toNat) v) :
    ∀ a : ((E.ssData p).page ↑((r-E.r₀).toNat+1) : ModuleCat.{v} ℤ),
      a = 0 ∨ a = (E.ssData p).pageπ ↑((r-E.r₀).toNat+1) v := by
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let down := i ≫ D.pageπ ↑n
  have hzero (z : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ))
      (hz : down z = 0) : D.pageπ ↑(n+1) z = 0 := by
    apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) _).mpr
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) (i z)).mp hz
    change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hb
    dsimp only [i] at hb
    rw [Subobject.ofLE_arrow] at hb
    exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
  intro a
  haveI : Epi (D.pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ↑(n+1))).mp inferInstance a
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


theorem represents_next_nonzero_of_incoming_zero
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    (hin : E.d r (p-E.diffDeg r) = 0)
    {x : E.Page 2 p} {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) : a ≠ 0 := by
  obtain ⟨_, z, hz, hza⟩ := ha
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n,m]
    exact_mod_cast (show (r-E.r₀).toNat ≤ (r+1-E.r₀).toNat by omega)
  have hB : D.B m = D.B n := by
    have hh := boundaries_succ_of_zero E r hr0 (p-E.diffDeg r) hin
    have hi : (r+1-E.r₀).toNat = (r-E.r₀).toNat+1 := by omega
    have hp : p-E.diffDeg r+E.diffDeg r = p := by abel
    rw [hp] at hh
    simpa only [D,n,m,hi] using hh
  let i := Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm)
  have hb' : RepresentsOnPage E r p x (D.pageπ n (i z)) := by
    refine ⟨hr,i z,?_,rfl⟩
    change ((Subobject.ofLE _ _ (D.Z_anti hnm)) ≫
      Subobject.ofLE _ _ _ ≫ D.pageπ _) z = x
    rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  intro ha0
  apply hne
  rw [represents_unique hb hb']
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mpr
  have hm := (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) z).mp (hza.trans ha0)
  rw [hB] at hm
  change (i ≫ (D.Z n).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


theorem differential_target_later_zero
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    (h : HasDifferential E r p q x y) : RepresentsOnPage E t q y 0 := by
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


theorem represents_add_tail
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x+y) (a+b) := by
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩


theorem sixth_zero_of_second_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x = 0 → RepresentsOnPage E 6 p x 0) :
    Subsingleton (E.Page 6 p) := by
  have hz (a : E.Page 6 p) : a=0 := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(6-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(6-E.r₀).toNat)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
      exact_mod_cast (show (2-E.r₀).toNat ≤ (6-E.r₀).toNat by omega))) ≫ A.pageπ _) z
    have hx : RepresentsOnPage E 6 p x a := ⟨by decide,z,rfl,hz⟩
    have hself : RepresentsOnPage E 2 p x x := by
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hx
      have hh := hb.eq_on_page_two
      simpa only [hh] using hb
    have hc : E.d 2 p x = 0 := represents_d_zero_of_later hstart (by decide) hself ⟨a,hx⟩
    exact represents_unique hx (hker x hc)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩


theorem fifth_frame_of_second_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ) (v : E.Page 5 p)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x = 0 →
      ∃ a : E.Page 5 p, RepresentsOnPage E 5 p x a ∧ (a=0 ∨ a=v)) :
    ∀ a : E.Page 5 p, a=0 ∨ a=v := by
  intro a
  let A := E.ssData p
  haveI : Epi (A.pageπ ↑(5-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(5-E.r₀).toNat)).mp inferInstance a
  let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
    exact_mod_cast (show (2-E.r₀).toNat ≤ (5-E.r₀).toNat by omega))) ≫ A.pageπ _) z
  have hx : RepresentsOnPage E 5 p x a := ⟨by decide,z,rfl,hz⟩
  have hself : RepresentsOnPage E 2 p x x := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hx
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hc : E.d 2 p x=0 := represents_d_zero_of_later hstart (by decide) hself ⟨a,hx⟩
  obtain ⟨b,hb,hcases⟩ := hker x hc
  rw [represents_unique hx hb]
  exact hcases



theorem fifth_zero_of_second_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x = 0 → RepresentsOnPage E 5 p x 0) :
    Subsingleton (E.Page 5 p) := by
  classical
  have hz (a : E.Page 5 p) : a=0 := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(5-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(5-E.r₀).toNat)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
      exact_mod_cast (show (2-E.r₀).toNat ≤ (5-E.r₀).toNat by omega))) ≫ A.pageπ _) z
    have hx : RepresentsOnPage E 5 p x a := ⟨by decide,z,rfl,hz⟩
    have hself : RepresentsOnPage E 2 p x x := by
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hx
      have hh := hb.eq_on_page_two
      simpa only [hh] using hb
    have hc : E.d 2 p x = 0 := represents_d_zero_of_later hstart (by decide) hself ⟨a,hx⟩
    exact represents_unique hx (hker x hc)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩


theorem fifth_zero_of_all_basis
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {n : ℕ}
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ F2))
    (he : ∀ i, RepresentsOnPage E 5 p (e.symm (Finsupp.single i 1)) 0) :
    Subsingleton (E.Page 5 p) := by
  classical
  have hz (a : E.Page 5 p) : a=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤5) e (fun _=>0) he a
    simpa using hc
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩


theorem frame_after_second
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} (hs : E.r₀≤2) (hr : 3≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2))
    {a : E.Page r p} (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
    (hn : E.d 2 p (e.symm (Finsupp.single 1 1)) ≠ 0) :
    ∀ q : E.Page r p, q=0 ∨ q=a := by
  classical
  have hz0 : E.d 2 p (e.symm (Finsupp.single 0 1)) = 0 := by
    obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hz.eq_on_page_two] at hz
    exact represents_d_zero_of_later hs (by omega) hz ⟨a,ha⟩
  intro q
  let A := E.ssData p
  haveI : Epi (A.pageπ ↑(r-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(r-E.r₀).toNat)).mp inferInstance q
  let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega))) ≫ A.pageπ _) z
  have hx : RepresentsOnPage E r p x q := ⟨by omega,z,rfl,hz⟩
  have hc : E.d 2 p x = 0 := by
    obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) hx
    rw [←hz.eq_on_page_two] at hz
    exact represents_d_zero_of_later hs (by omega) hz ⟨q,hx⟩
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize h0 : e x 0 = c0 at hxe
  generalize h1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,map_zero] at hxe
    rw [hxe] at hx
    exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by omega)))
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add] at hxe
    exact (hn (by simpa only [hxe] using hc)).elim
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx
    exact Or.inr (represents_unique hx ha)
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    exact (hn (by simpa only [hxe,map_add,hz0,zero_add] using hc)).elim


theorem third_zero_of_second_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x = 0 → RepresentsOnPage E 3 p x 0) :
    Subsingleton (E.Page 3 p) := by
  classical
  have hz (a : E.Page 3 p) : a=0 := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(3-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(3-E.r₀).toNat)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
      exact_mod_cast (show (2-E.r₀).toNat ≤ (3-E.r₀).toNat by omega))) ≫ A.pageπ _) z
    have hx : RepresentsOnPage E 3 p x a := ⟨by decide,z,rfl,hz⟩
    have hself : RepresentsOnPage E 2 p x x := by
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      have hh := hb.eq_on_page_two
      simpa only [hh] using hb
    have hc : E.d 2 p x = 0 := represents_d_zero_of_later hstart (by decide) hself ⟨a,hx⟩
    exact represents_unique hx (hker x hc)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩


theorem fourth_d_zero_of_second_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x = 0 →
      ∃ a : E.Page 4 p, RepresentsOnPage E 4 p x a ∧ E.d 4 p a=0) : E.d 4 p = 0 := by
  classical
  ext a
  let A := E.ssData p
  haveI : Epi (A.pageπ ↑(4-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(4-E.r₀).toNat)).mp inferInstance a
  let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
    exact_mod_cast (show (2-E.r₀).toNat ≤ (4-E.r₀).toNat by omega))) ≫ A.pageπ _) z
  have hx : RepresentsOnPage E 4 p x a := ⟨by decide,z,rfl,hz⟩
  have hself : RepresentsOnPage E 2 p x x := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hx
    have hh := hb.eq_on_page_two
    simpa only [hh] using hb
  have hc : E.d 2 p x=0 := represents_d_zero_of_later hstart (by decide) hself ⟨a,hx⟩
  obtain ⟨b,hb,hdb⟩ := hker x hc
  rw [represents_unique hx hb]
  exact hdb


theorem vx_nonzero_no_incoming
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ×ℤ}
    (hr0 : E.r₀≤2) (hin : ∀ r : ℤ, 2≤r → E.d r (p-E.diffDeg r)=0)
    {r : ℤ} {x : E.Page 2 p} {a : E.Page r p}
    (ha : RepresentsOnPage E r p x a) (hn : x≠0) : a≠0 := by
  classical
  obtain ⟨hr,z,hz,hza⟩ := ha
  let A := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  let m : WithTop ℕ := ↑(r-E.r₀).toNat
  have hnm : n≤m := by
    dsimp only [n,m]
    exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega)
  let i := Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)
  have hB : A.B ⊤=A.B n := boundaries_top_eq_of_d_eq_zero E 2 hr0 p hin
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show m≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply hn
  rw [←hz]
  change A.pageπ n (i z)=0
  apply (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z n).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


theorem pq_rep3zero_boundary
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ×ℤ} {x : E.Page 2 p}
    (h : RepresentsOnPage E 3 p x 0) : IsBoundaryBy E 2 p x := by
  classical
  obtain ⟨_,z,hzx,hz0⟩ := h
  let A := E.ssData p
  let m : WithTop ℕ := ↑(3-E.r₀).toNat
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  have hm := (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mp hz0
  obtain ⟨b,hb⟩ := hm
  refine ⟨by decide,?_⟩
  refine ⟨b,?_⟩
  have heq : (Subobject.ofLE (A.B m) (A.B ⊤) (A.B_mono le_top) ≫
      Subobject.ofLE (A.B ⊤) (A.Z ⊤) (A.B_le_Z ⊤) ≫
      Subobject.ofLE (A.Z ⊤) (A.Z n) (A.Z_anti le_top)) b =
      (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti (by dsimp only [n,m]; exact_mod_cast (show (2-E.r₀).toNat ≤ (3-E.r₀).toNat by omega)))) z := by
    apply (ModuleCat.mono_iff_injective (A.Z n).arrow).mp inferInstance
    change (Subobject.ofLE _ _ _ ≫ Subobject.ofLE _ _ _ ≫ Subobject.ofLE _ _ _ ≫ (A.Z n).arrow) b =
      (Subobject.ofLE _ _ _ ≫ (A.Z n).arrow) z
    simpa only [Category.assoc,Subobject.ofLE_arrow] using hb
  exact (congrArg (fun v => A.pageπ n v) heq).trans hzx

theorem represents_sub_tail
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ}
    {x y : E.Page 2 p} {a b : E.Page r p}
    (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x-y) (a-b) := by
  classical
  obtain ⟨hr,z,hz,hza⟩ := ha
  obtain ⟨_,w,hw,hwb⟩ := hb
  exact ⟨hr,z-w,by rw [map_sub,hz,hw],by rw [map_sub,hza,hwb]⟩


theorem page_has_representative
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ}
    (hr : 2≤r) (a : E.Page r p) : ∃ x, RepresentsOnPage E r p x a := by
  classical
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  haveI : Epi (A.pageπ n) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ n)).mp inferInstance a
  let x := (Subobject.ofLE (A.Z n) (A.Z ↑(2-E.r₀).toNat) (A.Z_anti (by
    dsimp only [n]
    exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ ↑(2-E.r₀).toNat) z
  exact ⟨x,hr,z,rfl,hz⟩


theorem reaches_from_support
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ×ℤ} {r : ℤ} (hr : 2≤r) {N : ℕ}
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2)) (x : E.Page 2 p)
    (hv : ∀ i, e x i≠0 → ReachesPage E r p (e.symm (Finsupp.single i 1))) :
    ReachesPage E r p x := by
  classical
  classical
  let c : Fin N → F2 := e x
  have hsum (s : Finset (Fin N)) :
      ReachesPage E r p (∑ i ∈ s, if c i=0 then 0 else e.symm (Finsupp.single i 1)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (show ReachesPage E r p 0 from ⟨0,RepresentsOnPage.zero hr⟩)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      by_cases hc : c i=0
      · simpa only [hc,ite_true,zero_add] using ih
      · obtain ⟨a,ha⟩ := hv i hc
        obtain ⟨b,hb⟩ := ih
        refine ⟨a+b,?_⟩
        simpa only [hc,ite_false] using represents_add_tail ha hb
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
  obtain ⟨a,ha⟩ := hsum Finset.univ
  exact ⟨a,by simpa only [hx] using ha⟩


theorem d_zero_of_second_kernel_extends
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (hs : E.r₀≤2) {p : ℤ×ℤ} {r : ℤ} (hr : 3≤r)
    (hext : ∀ x : E.Page 2 p, E.d 2 p x=0 → ReachesPage E (r+1) p x) : E.d r p=0 := by
  classical
  ext a
  change E.d r p a=0
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  haveI : Epi (A.pageπ n) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ n)).mp inferInstance a
  let x := (Subobject.ofLE (A.Z n) (A.Z ↑(2-E.r₀).toNat) (A.Z_anti (by
    dsimp only [n]
    exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ ↑(2-E.r₀).toNat) z
  have hxa : RepresentsOnPage E r p x a := ⟨by omega,z,rfl,hz⟩
  obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) hxa
  have hx2 : E.d 2 p x=0 := by
    have hh := represents_d_zero_of_later hs (by omega : (2:ℤ)<r) ha2 ⟨a,hxa⟩
    simpa only [ha2.eq_on_page_two] using hh
  exact represents_d_zero_of_later (by omega) (by omega : r<r+1) hxa (hext x hx2)


theorem reaches_before {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t) (ht : ReachesPage E t p x) : ReachesPage E r p x := by
  obtain ⟨a,_,z,hz,_⟩ := ht
  let D := E.ssData p
  have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑(t-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z ↑(t-E.r₀).toNat) (D.Z ↑(r-E.r₀).toNat) (D.Z_anti hrt')) z
  refine ⟨D.pageπ _ zr,hr,zr,?_,rfl⟩
  dsimp only [zr]
  rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

theorem choice_frame_of_three_basis
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ}
    (hr : 2<r) (hr0 : E.r₀≤2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2))
    (b0 b1 b2 : E.Page 2 p)
    (he0 : e.symm (Finsupp.single 0 1)=b0)
    (he1 : e.symm (Finsupp.single 1 1)=b1)
    (he2 : e.symm (Finsupp.single 2 1)=b2)
    (a : E.Page r p) (ha : RepresentsOnPage E r p b1 a)
    (hz : RepresentsOnPage E r p b2 0)
    (hd0 : E.d 2 p b0≠0) : ∀ y:E.Page r p,y=0∨y=a := by
  classical
  have dz {x : E.Page 2 p} {b : E.Page r p}
      (hb : RepresentsOnPage E r p x b) : E.d 2 p x=0 := by
    obtain ⟨b2,hb2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ⟨b,hb⟩
    have hh := represents_d_zero_of_later hr0 hr hb2 ⟨b,hb⟩
    simpa only [hb2.eq_on_page_two] using hh
  have hd1 := dz ha
  have hd2 := dz hz
  have hadd : RepresentsOnPage E r p (b1+b2) a := by
    obtain ⟨hr',z,hz',hza⟩ := ha
    obtain ⟨_,w,hw,hwb⟩ := hz
    refine ⟨hr',z+w,by rw [map_add,hz',hw],?_⟩
    rw [map_add,hza,hwb,add_zero]
  intro y
  let A := E.ssData p
  let m : WithTop ℕ := ↑(r-E.r₀).toNat
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  have hnm : n≤m := by
    dsimp only [n,m]
    exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega)
  haveI : Epi (A.pageπ m) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hy⟩ := (ModuleCat.epi_iff_surjective (A.pageπ m)).mp inferInstance y
  let x := (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z
  have hxrep : RepresentsOnPage E r p x y := ⟨by omega,z,rfl,hy⟩
  have hx : E.d 2 p x=0 := dz hxrep
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x=e.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)+Finsupp.single 2 (0:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx hxrep
    left
    apply represents_unique hxrep
    exact RepresentsOnPage.zero (by omega)
  · change x=e.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)+Finsupp.single 2 (1:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,he2] at hxe
    rw [hxe] at hx hxrep
    left
    apply represents_unique hxrep
    exact hz
  · change x=e.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)+Finsupp.single 2 (0:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,he1] at hxe
    rw [hxe] at hx hxrep
    right
    apply represents_unique hxrep
    exact ha
  · change x=e.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)+Finsupp.single 2 (1:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,he1,he2] at hxe
    rw [hxe] at hx hxrep
    right
    apply represents_unique hxrep
    exact hadd
  · change x=e.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)+Finsupp.single 2 (0:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,he0] at hxe
    rw [hxe] at hx hxrep
    simp only [] at hx
    exact (hd0 hx).elim
  · change x=e.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)+Finsupp.single 2 (1:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he2] at hxe
    rw [hxe] at hx hxrep
    simp only [map_add,hd2,add_zero] at hx
    exact (hd0 hx).elim
  · change x=e.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)+Finsupp.single 2 (0:KIP126.Algebra.F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he1] at hxe
    rw [hxe] at hx hxrep
    simp only [map_add,hd1,add_zero] at hx
    exact (hd0 hx).elim
  · change x=e.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)+Finsupp.single 2 (1:KIP126.Algebra.F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    rw [hxe] at hx hxrep
    simp only [map_add,hd1,hd2,add_zero] at hx
    exact (hd0 hx).elim

theorem choice_single_basis_zero_page
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ}
    (hr : 2≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2))
    (b : E.Page 2 p) (he : e.symm (Finsupp.single 0 1)=b)
    (hb : RepresentsOnPage E r p b 0) : Subsingleton (E.Page r p) := by
  classical
  have hall (y : E.Page r p) : y=0 := by
    let A := E.ssData p
    let m : WithTop ℕ := ↑(r-E.r₀).toNat
    let n : WithTop ℕ := ↑(2-E.r₀).toNat
    have hnm : n≤m := by
      dsimp only [n,m]
      exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega)
    haveI : Epi (A.pageπ m) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hy⟩ := (ModuleCat.epi_iff_surjective (A.pageπ m)).mp inferInstance y
    let x := (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z
    have hxrep : RepresentsOnPage E r p x y := ⟨hr,z,rfl,hy⟩
    have heq : e x=Finsupp.single 0 (e x 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc : e x 0=c at hxe
    fin_cases c
    · change x=e.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)) at hxe
      simp only [Finsupp.single_zero,map_zero] at hxe
      rw [hxe] at hxrep
      exact represents_unique hxrep (RepresentsOnPage.zero hr)
    · change x=e.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)) at hxe
      rw [he] at hxe
      rw [hxe] at hxrep
      exact represents_unique hxrep hb
  exact ⟨fun x y=>(hall x).trans (hall y).symm⟩

theorem choice_next_zero_of_single_frame_nonzero_differential
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ}
    (hr : 2≤r) (hr0 : E.r₀≤r)
    (a : E.Page r p) (ha : E.d r p a≠0) (hall : ∀b:E.Page r p,b=0∨b=a) :
    Subsingleton (E.Page (r+1) p) := by
  classical
  have hzero (y:E.Page (r+1) p) : y=0 := by
    let A := E.ssData p
    let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
    let n : WithTop ℕ := ↑(r-E.r₀).toNat
    let n0 : WithTop ℕ := ↑(2-E.r₀).toNat
    have hnm : n≤m := by
      dsimp only [n,m]
      exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
    have hn0 : n0≤n := by
      dsimp only [n0,n]
      exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega)
    haveI : Epi (A.pageπ m) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hy⟩ := (ModuleCat.epi_iff_surjective (A.pageπ m)).mp inferInstance y
    let x := (Subobject.ofLE (A.Z m) (A.Z n0) (A.Z_anti (hn0.trans hnm)) ≫ A.pageπ n0) z
    let i := Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)
    let b := A.pageπ n (i z)
    have hty : RepresentsOnPage E (r+1) p x y := ⟨by omega,z,rfl,hy⟩
    have hbr : RepresentsOnPage E r p x b := by
      refine ⟨hr,i z,?_,rfl⟩
      dsimp only [i,x]
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    have hdb : E.d r p b=0 := represents_d_zero_of_later hr0 (by omega) hbr ⟨y,hty⟩
    have hb : b=0 := (hall b).resolve_right (fun he=>ha (he ▸ hdb))
    rw [←hy]
    apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
    have hh := (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z _) _).mp hb
    have he : (A.Z n).arrow (i z)=(A.Z m).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (A.Z_anti hnm)) z
    rw [he] at hh
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) hh
  exact ⟨fun x y=>(hzero x).trans (hzero y).symm⟩


theorem d_zero_of_complete_representatives
    {ESeq : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {n : ℕ} (hr : 2 ≤ r)
    (e : ESeq.Page 2 p ≃ₗ[ℤ] (Fin n →₀ KIP126.Algebra.F2))
    (hb : ∀ i : Fin n, ∃ xr : ESeq.Page r p,
      RepresentsOnPage ESeq r p (e.symm (Finsupp.single i 1)) xr ∧ ESeq.d r p xr = 0) :
    ESeq.d r p = 0 := by
  have hall (f : Fin n →₀ KIP126.Algebra.F2) :
      ∃ xr : ESeq.Page r p, RepresentsOnPage ESeq r p (e.symm f) xr ∧ ESeq.d r p xr = 0 := by
    induction f using Finsupp.induction with
    | zero => exact ⟨0, (map_zero e.symm) ▸ RepresentsOnPage.zero hr, map_zero _⟩
    | @single_add i a f hi ha ih =>
      fin_cases a
      · simpa using ih
      · obtain ⟨xr,hxr,hdx⟩ := hb i
        obtain ⟨yr,hyr,hdy⟩ := ih
        exact ⟨xr+yr, (map_add e.symm _ _) ▸ represents_add_tail hxr hyr, by rw [map_add,hdx,hdy,zero_add]⟩
  ext yr
  haveI : Epi ((ESeq.ssData p).pageπ ↑(r-ESeq.r₀).toNat) := by
    change Epi (cokernel.π _)
    infer_instance
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((ESeq.ssData p).pageπ ↑(r-ESeq.r₀).toNat)).mp inferInstance yr
  let x : ESeq.Page 2 p := (Subobject.ofLE _ _ ((ESeq.ssData p).Z_anti
    (by exact_mod_cast (show (2-ESeq.r₀).toNat ≤ (r-ESeq.r₀).toNat by omega))) ≫
    (ESeq.ssData p).pageπ ↑(2-ESeq.r₀).toNat) z
  have hrep : RepresentsOnPage ESeq r p x ((ESeq.ssData p).pageπ ↑(r-ESeq.r₀).toNat z) :=
    ⟨hr,z,rfl,rfl⟩
  obtain ⟨xr,hxr,hdx⟩ := hall (e x)
  rw [LinearEquiv.symm_apply_apply] at hxr
  rw [represents_unique hrep hxr]
  exact hdx


theorem page_eq_sum_of_complete_representatives
    {ESeq : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {n : ℕ} (hr : 2 ≤ r)
    (e : ESeq.Page 2 p ≃ₗ[ℤ] (Fin n →₀ KIP126.Algebra.F2))
    (xr : Fin n → ESeq.Page r p)
    (hb : ∀ i : Fin n, RepresentsOnPage ESeq r p (e.symm (Finsupp.single i 1)) (xr i))
    (a : ESeq.Page r p) :
    ∃ c : Fin n → KIP126.Algebra.F2, a = ∑ i, if c i = 0 then 0 else xr i := by
  classical
  have htwo (i : Fin n) : xr i + xr i = 0 := by
    have hh := represents_add_tail (hb i) (hb i)
    have he : e.symm (Finsupp.single i 1) + e.symm (Finsupp.single i 1) = 0 := by
      rw [← map_add, ← Finsupp.single_add]
      have h2 : (1 : KIP126.Algebra.F2)+1 = 0 := rfl
      rw [h2,Finsupp.single_zero,map_zero]
    rw [he] at hh
    exact represents_unique hh (RepresentsOnPage.zero hr)
  have hadd2 : (1 : KIP126.Algebra.F2)+1 = 0 := rfl
  let φ (i : Fin n) : KIP126.Algebra.F2 →+ ESeq.Page r p :=
    { toFun := fun c => if c=0 then 0 else xr i
      map_zero' := by simp
      map_add' := by
        intro a b
        fin_cases a <;> fin_cases b <;> simp [htwo,hadd2] }
  let Φ := Finsupp.liftAddHom φ
  have hrep (f : Fin n →₀ KIP126.Algebra.F2) :
      RepresentsOnPage ESeq r p (e.symm f) (Φ f) := by
    induction f using Finsupp.induction with
    | zero => simpa only [map_zero] using (RepresentsOnPage.zero (E := ESeq) (p := p) hr)
    | @single_add i a f hi ha ih =>
      fin_cases a
      · simpa using ih
      · rw [map_add,map_add]
        apply represents_add_tail _ ih
        simpa only [Φ,Finsupp.liftAddHom_apply_single,φ,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
          show (⟨1,by decide⟩ : KIP126.Algebra.F2) = 1 from rfl, one_ne_zero, ite_false] using hb i
  haveI : Epi ((ESeq.ssData p).pageπ ↑(r-ESeq.r₀).toNat) := by
    change Epi (cokernel.π _)
    infer_instance
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((ESeq.ssData p).pageπ ↑(r-ESeq.r₀).toNat)).mp inferInstance a
  let x : ESeq.Page 2 p := (Subobject.ofLE _ _ ((ESeq.ssData p).Z_anti
    (by exact_mod_cast (show (2-ESeq.r₀).toNat ≤ (r-ESeq.r₀).toNat by omega))) ≫
    (ESeq.ssData p).pageπ ↑(2-ESeq.r₀).toNat) z
  have hx : RepresentsOnPage ESeq r p x a := ⟨hr,z,rfl,hz⟩
  have hy := hrep (e x)
  rw [LinearEquiv.symm_apply_apply] at hy
  refine ⟨e x, ?_⟩
  rw [represents_unique hx hy]
  change Finsupp.sum (e x) (fun i c => if c=0 then 0 else xr i) = _
  exact Finsupp.sum_fintype _ _ (fun _ => by simp)


theorem same_boundaries_projection_eq
    (A : SSData (ModuleCat.{v} ℤ))
    (n m : WithTop ℕ) (hnm : n ≤ m) (hB : A.B m = A.B n)
    (z z' : (Subobject.underlying.obj (A.Z m) : ModuleCat.{v} ℤ))
    (hz : A.pageπ m z = A.pageπ m z') :
    (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z =
    (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z' := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  have hz0 : A.pageπ m (z-z') = 0 := by rw [map_sub,hz,sub_self]
  have hm := (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z m) (z-z')).mp hz0
  rw [hB] at hm
  change A.pageπ n ((Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) (z-z')) = 0
  apply (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z n) _).mpr
  change (Subobject.ofLE (A.Z m) (A.Z n) _ ≫ (A.Z n).arrow) (z-z') ∈ _
  rwa [Subobject.ofLE_arrow]


theorem middle_add {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x+y) (a+b) := by
  classical
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩


theorem middle_if {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
    (c : F2) (h : RepresentsOnPage E r p x a) :
    RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
  classical
  split
  · exact RepresentsOnPage.zero h.1
  · exact h


theorem middle_rep2 {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r)
    (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
  classical
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
  rw [←hb.eq_on_page_two] at hb
  exact hb


theorem reaches_earlier {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hr : 2 ≤ r) (hrt : r ≤ t)
    (ht : ReachesPage E t p x) : ReachesPage E r p x := by
  classical
  obtain ⟨_, _, z, hz, _⟩ := ht
  let A := E.ssData p
  let m : WithTop ℕ := ↑(t-E.r₀).toNat
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n,m]
    exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
  let z' := (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) z
  refine ⟨A.pageπ n z', hr, z', ?_, rfl⟩
  dsimp only [z']
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz


theorem represents_sub {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {a b : E.Page 2 p} {ar br : E.Page r p}
    (ha : RepresentsOnPage E r p a ar) (hb : RepresentsOnPage E r p b br) :
    RepresentsOnPage E r p (a-b) (ar-br) := by
  classical
  obtain ⟨hr,z,hz,hzr⟩ := ha
  obtain ⟨_,w,hw,hwr⟩ := hb
  exact ⟨hr,z-w,by rw [map_sub,hz,hw],by rw [map_sub,hzr,hwr]⟩


theorem differential_target_cycle {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q} (h : HasDifferential E r p q x y) :
    ∃ yr : E.Page r q, RepresentsOnPage E r q y yr ∧ E.d r q yr = 0 := by
  classical
  obtain ⟨rfl,xr,yr,_,hy,hd⟩ := h
  simp only [eqToHom_refl, Category.comp_id] at hd
  exact ⟨yr,hy,IsPageBoundary.d_eq_zero ⟨xr,hd⟩⟩


theorem represents_two_self {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
  classical
  haveI : Epi ((E.ssData p).pageπ ↑(2-E.r₀).toNat) := by
    change Epi (cokernel.π _)
    infer_instance
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ ↑(2-E.r₀).toNat)).mp inferInstance x
  exact ⟨le_rfl,z,by simpa only [Subobject.ofLE_refl,Category.id_comp] using hz,hz⟩


theorem represents_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hrt : r ≤ t)
    (hr : RepresentsOnPage E r p x 0) {y : E.Page t p}
    (ht : RepresentsOnPage E t p x y) : y = 0 := by
  classical
  obtain ⟨_,z,hz,hzy⟩ := ht
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑(t-E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n,m]
    exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
  let z' := (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) z
  have hrep : RepresentsOnPage E r p x (A.pageπ n z') := by
    refine ⟨hr.1,z',?_,rfl⟩
    dsimp only [z']
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have hh := (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z _) _).mp
    (represents_unique hrep hr)
  have hh' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) hh
  rw [← hzy]
  apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
  change (Subobject.ofLE (A.Z m) (A.Z n) _ ≫ (A.Z n).arrow) z ∈ _ at hh'
  rwa [Subobject.ofLE_arrow] at hh'


theorem page_has_initial_representative {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r) (a : E.Page r p) :
    ∃ x : E.Page 2 p, RepresentsOnPage E r p x a := by
  classical
  haveI : Epi ((E.ssData p).pageπ ↑(r-E.r₀).toNat) := by
    change Epi (cokernel.π _)
    infer_instance
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ ↑(r-E.r₀).toNat)).mp inferInstance a
  exact ⟨_,hr,z,rfl,hz⟩


theorem represents_transport_eq {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {t : ℤ} {x y : E.Page 2 p}
    {ar : E.Page r p} {a b : E.Page t p} (hrt : r ≤ t)
    (hx : RepresentsOnPage E r p x ar) (hy : RepresentsOnPage E r p y ar)
    (hxt : RepresentsOnPage E t p x a) (hyt : RepresentsOnPage E t p y b) : a = b := by
  classical
  apply sub_eq_zero.mp
  exact represents_later_zero hrt
    (by simpa only [sub_self] using represents_sub hx hy) (represents_sub hxt hyt)


theorem represents_bit {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (c : KIP126.Algebra.F2) {x : E.Page 2 p} {a : E.Page r p}
    (h : RepresentsOnPage E r p x a) :
    RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
  classical
  by_cases hc : c=0
  · simpa only [hc,ite_true] using (RepresentsOnPage.zero (E := E) (p := p) h.1)
  · simpa only [hc,ite_false] using h


theorem differential_two_direct {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 (p+E.diffDeg 2)}
    (h : HasDifferential E 2 p (p+E.diffDeg 2) x y) : E.d 2 p x = y := by
  classical
  obtain ⟨_,hd⟩ := h.eq_on_page_two
  simpa only [eqToHom_refl,Category.comp_id] using hd



theorem f2_expand {N : ℕ} (f : Fin N →₀ F2) :
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

theorem generated_one {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
    (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
    (x : E.Page r p) : x=0 ∨ x=a := by
  have hv (i : Fin 1) : RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) a := by
    fin_cases i
    exact ha
  obtain ⟨c,hc⟩ := page_generated_from_representatives hr e (fun _ => a) hv x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
  by_cases h : c 0=0
  · exact Or.inl (by simpa only [h,ite_true] using hc)
  · exact Or.inr (by simpa only [h,ite_false] using hc)

theorem generated_two {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
    (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
    (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
    (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
  let vv : Fin 2 → E.Page r p := ![a,b]
  have hv (i : Fin 2) : RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) (vv i) := by
    fin_cases i
    · exact ha
    · exact hb
  obtain ⟨c,hc⟩ := page_generated_from_representatives hr e vv hv x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
  change x=(if c 0=0 then 0 else a)+(if c 1=0 then 0 else b) at hc
  by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
  all_goals simp only [h0,h1,ite_true,ite_false,zero_add,add_zero] at hc
  · exact Or.inl hc
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inr hc))


theorem fourth_zero_of_three_basis
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} (hstart : E.r₀ ≤ 2) {p : ℤ × ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 3 →₀ F2))
      (y0 y1 : E.Page 2 (p+E.diffDeg 3))
      (h0 : HasDifferential E 3 p (p+E.diffDeg 3) (e.symm (Finsupp.single 0 1)) y0)
      (h1 : HasDifferential E 3 p (p+E.diffDeg 3) (e.symm (Finsupp.single 1 1)) y1)
      (hz : RepresentsOnPage E 3 p (e.symm (Finsupp.single 2 1)) 0)
      (hin : E.d 2 (p+E.diffDeg 3-E.diffDeg 2)=0)
      (hn0 : y0≠0) (hn1 : y1≠0) (hn01 : y0+y1≠0) : Subsingleton (E.Page 4 p) := by
  classical
  obtain ⟨_,a0,b0,ha0,hb0,hd0⟩ := h0
  obtain ⟨_,a1,b1,ha1,hb1,hd1⟩ := h1
  change E.d 3 p a0=b0 at hd0
  change E.d 3 p a1=b1 at hd1
  have n0 := represents_next_nonzero_of_incoming_zero (E := E) (r := 2) (p := p+E.diffDeg 3) (by omega) (by decide) hin hb0 (represents_two_self _) hn0
  have n1 := represents_next_nonzero_of_incoming_zero (E := E) (r := 2) (p := p+E.diffDeg 3) (by omega) (by decide) hin hb1 (represents_two_self _) hn1
  have n01 := represents_next_nonzero_of_incoming_zero (E := E) (r := 2) (p := p+E.diffDeg 3) (by omega) (by decide) hin (represents_add_tail hb0 hb1) (represents_two_self _) hn01
  have ker (a : E.Page 3 p) (ha : E.d 3 p a=0) : a=0 := by
    let vv : Fin 3 → E.Page 3 p := ![a0,a1,0]
    have hv (i : Fin 3) : RepresentsOnPage E 3 p (e.symm (Finsupp.single i 1)) (vv i) := by
      fin_cases i
      · exact ha0
      · exact ha1
      · exact hz
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    change a=(if c 0=0 then 0 else a0)+((if c 1=0 then 0 else a1)+(if c 2=0 then 0 else 0)) at hc
    simp only [ite_self,add_zero] at hc
    by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
    all_goals simp only [h0,h1,ite_true,ite_false,zero_add,add_zero] at hc
    · exact hc
    · exact (n1 (by simpa only [hc,hd1] using ha)).elim
    · exact (n0 (by simpa only [hc,hd0] using ha)).elim
    · exact (n01 (by simpa only [hc,map_add,hd0,hd1] using ha)).elim
  let S := E.pageShortComplex 3 (p-E.diffDeg 3)
  have kerS : ∀ a : S.X₂, S.g a=0 → a=0 := by
    change ∀ a : E.Page 3 (p-E.diffDeg 3+E.diffDeg 3), E.d 3 (p-E.diffDeg 3+E.diffDeg 3) a=0 → a=0
    rw [sub_add_cancel]
    exact ker
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [kerS a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 p
    (by omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))


theorem next_page_zero_of_kernel
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} (hr : E.r₀ ≤ r)
    (hker : ∀ x : E.Page r p, E.d r p x = 0 → x = 0) :
    Subsingleton (E.Page (r+1) p) := by
  let S := E.pageShortComplex r (p-E.diffDeg r)
  have kerS : ∀ x : S.X₂, S.g x = 0 → x = 0 := by
    change ∀ x : E.Page r (p-E.diffDeg r+E.diffDeg r),
      E.d r (p-E.diffDeg r+E.diffDeg r) x = 0 → x = 0
    rw [sub_add_cancel]
    exact hker
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [kerS x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E r p hr).isZero_iff.mpr
    ((S.exact_iff_isZero_homology).mp hs))
theorem finite_basis_expansion {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
    (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (a : A) :
    a=∑ i : Fin N, if (e a) i=0 then 0 else e.symm (Finsupp.single i 1) := by
  apply e.injective
  rw [map_sum]
  ext i
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · generalize (e a) i=b
    fin_cases b <;> simp
  · intro j hj hji
    by_cases hc : (e a) j=0
    · simp [hc]
    · simp [hc,hji]
  · simp

theorem fourth_frame_of_four_basis
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} (hstart : E.r₀ ≤ 2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 4 →₀ F2))
    (f : E.Page 2 (p+E.diffDeg 2) ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (a b c : E.Page 4 p)
    (ha : RepresentsOnPage E 4 p
      (e.symm (Finsupp.single 0 1)+e.symm (Finsupp.single 1 1)) a)
    (hb : RepresentsOnPage E 4 p (e.symm (Finsupp.single 2 1)) b)
    (hc : RepresentsOnPage E 4 p (e.symm (Finsupp.single 3 1)) c)
    (d0 : E.d 2 p (e.symm (Finsupp.single 0 1))=f.symm (Finsupp.single 0 1))
    (d1 : E.d 2 p (e.symm (Finsupp.single 1 1))=f.symm (Finsupp.single 0 1))
    (d2 : E.d 2 p (e.symm (Finsupp.single 2 1))=0)
    (d3 : E.d 2 p (e.symm (Finsupp.single 3 1))=0)
    (z : E.Page 4 p) :
    z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c := by
  classical
  let b0 := e.symm (Finsupp.single (0:Fin 4) 1)
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1)=b0 := rfl
  let b1 := e.symm (Finsupp.single (1:Fin 4) 1)
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1)=b1 := rfl
  let b2 := e.symm (Finsupp.single (2:Fin 4) 1)
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1)=b2 := rfl
  let b3 := e.symm (Finsupp.single (3:Fin 4) 1)
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1)=b3 := rfl
  change E.d 2 p b0=f.symm (Finsupp.single 0 1) at d0
  change E.d 2 p b1=f.symm (Finsupp.single 0 1) at d1
  change E.d 2 p b2=0 at d2
  change E.d 2 p b3=0 at d3
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1)=f.symm (Finsupp.single (0:Fin 2) 1) := rfl

  obtain ⟨x,hx⟩ := page_has_representative (by decide : (2:ℤ)≤4) z
  have dx : E.d 2 p x=0 :=
    represents_d_zero_of_later (by omega) (by decide : (2:ℤ)<4) (represents_two_self x) ⟨z,hx⟩
  have hex : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)) := by rw [←hex,LinearEquiv.symm_apply_apply]
  generalize h0 : e x 0=c0 at hxe
  generalize h1 : e x 1=c1 at hxe
  generalize h2 : e x 2=c2 at hxe
  generalize h3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
    exact Or.inl (represents_unique (by simpa only [hxe] using hx) (RepresentsOnPage.zero (by decide)))
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [he3] at hxe
    exact Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (hc)))
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [he2] at hxe
    exact Or.inr (Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (hb))))
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,map_add] at hxe
    rw [he2] at hxe
    rw [he3] at hxe
    exact Or.inr (Or.inr (Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (represents_add_tail (hb) hc)))))
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [he1] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [d1,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,map_add] at hxe
    rw [he1] at hxe
    rw [he3] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d1,d3,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,map_add] at hxe
    rw [he1] at hxe
    rw [he2] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d1,d2,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,map_add] at hxe
    rw [he1] at hxe
    rw [he2] at hxe
    rw [he3] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d1,d2,d3,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [he0] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [d0,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he3] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d0,d3,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he2] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d0,d2,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he2] at hxe
    rw [he3] at hxe
    have hh := congrArg (fun y => f y 0) dx
    rw [hxe] at hh
    simp only [map_add,d0,d2,d3,add_zero,LinearEquiv.apply_symm_apply,map_zero,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he1] at hxe
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (ha))))))
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he1] at hxe
    rw [he3] at hxe
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (represents_add_tail (ha) hc)))))))
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,map_add] at hxe
    rw [he0] at hxe
    rw [he1] at hxe
    rw [he2] at hxe
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (represents_unique (by simpa only [hxe] using hx) (represents_add_tail (ha) hb))))))))
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add] at hxe
    rw [he0] at hxe
    rw [he1] at hxe
    rw [he2] at hxe
    rw [he3] at hxe
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (represents_unique (by simpa only [hxe] using hx) (represents_add_tail (represents_add_tail (ha) hb) hc))))))))

theorem represents_next_nonzero_of_incoming_two_cases
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {q : ℤ × ℤ} (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {x : E.Page 2 (q+E.diffDeg r)} {a : E.Page (r+1) (q+E.diffDeg r)}
    {b c : E.Page r (q+E.diffDeg r)}
    (ha : RepresentsOnPage E (r+1) (q+E.diffDeg r) x a)
    (hb : RepresentsOnPage E r (q+E.diffDeg r) x b)
    (himage : ∀ v : E.Page r q, E.d r q v=0 ∨ E.d r q v=c)
    (hbne : b ≠ 0) (hbc : b-c ≠ 0) : a ≠ 0 := by
  obtain ⟨_,z,hz,hza⟩ := ha
  let D := E.ssData (q+E.diffDeg r)
  let n : ℕ := (r-E.r₀).toNat
  let m : ℕ := (r+1-E.r₀).toNat
  have hnm : n ≤ m := by dsimp only [n,m]; omega
  let i := Subobject.ofLE (D.Z ↑m) (D.Z ↑n) (D.Z_anti (by exact_mod_cast hnm))
  have hb' : RepresentsOnPage E r (q+E.diffDeg r) x (D.pageπ ↑n (i z)) := by
    as_aux_lemma =>
      refine ⟨hr,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE _ _ _ ≫ D.pageπ _) z = x
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz
  have heq : D.pageπ ↑n (i z)=b := represents_unique hb' hb
  let P (k : ℕ) : Prop := ∀ (hk : n ≤ k)
      (w : (Subobject.underlying.obj (D.Z ↑k) : ModuleCat.{v} ℤ)),
    D.pageπ ↑k w = 0 ↔
      (Subobject.ofLE (D.Z ↑k) (D.Z ↑n) (D.Z_anti (by exact_mod_cast hk)) ≫
        D.pageπ ↑n) w ∈ LinearMap.range (E.d r q).hom
  have hP : P (n+1) := by
    intro hk w
    exact next_projection_zero_iff_incoming E r hr0 q w
  have hi : m=n+1 := by dsimp only [m,n]; omega
  have hPm : P m := hi.symm ▸ hP
  intro ha0
  have hm := (hPm hnm z).mp (hza.trans ha0)
  change D.pageπ ↑n (i z) ∈ LinearMap.range (E.d r q).hom at hm
  rw [heq] at hm
  obtain ⟨v,hv⟩ := hm
  rcases himage v with hv0|hvc
  · exact hbne (hv.symm.trans hv0)
  · exact hbc (sub_eq_zero.mpr (hv.symm.trans hvc))

/-- Keep the source degree explicit when specializing the page passage lemma. -/
theorem represents_next_nonzero_of_incoming_zero_at
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ}
    {p q : ℤ × ℤ} (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    (hin : E.d r q=0)
    {x : E.Page 2 p} {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b≠0) (hdeg : q+E.diffDeg r=p := by first | rfl | simp only [sub_add_cancel]) : a≠0 := by
  subst p
  have hin' : E.d r ((q+E.diffDeg r)-E.diffDeg r)=0 := by
    exact (congrArg (fun k => E.d r k=0) (add_sub_cancel_right q (E.diffDeg r))).mpr hin
  exact represents_next_nonzero_of_incoming_zero hr0 hr hin' ha hb hne

/-- Separate the target degree from its arithmetic description during elaboration. -/
theorem represents_next_nonzero_of_incoming_two_cases_at
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p q : ℤ × ℤ} (hdeg : q+E.diffDeg r=p)
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {x : E.Page 2 p} {a : E.Page (r+1) p} {b c : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (himage : ∀ v : E.Page r q,
      (E.d r q ≫ eqToHom (congrArg (E.Page r) hdeg)) v=0 ∨
      (E.d r q ≫ eqToHom (congrArg (E.Page r) hdeg)) v=c)
    (hbne : b≠0) (hbc : b-c≠0) : a≠0 := by
  subst p
  simp only [eqToHom_refl,Category.comp_id] at himage
  exact represents_next_nonzero_of_incoming_two_cases hr0 hr ha hb himage hbne hbc

/-- An explicit target degree keeps the two complete coordinate systems separate. -/
theorem fourth_frame_of_four_basis_at
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p q : ℤ × ℤ} (hdeg : p+E.diffDeg 2=q) (hstart : E.r₀ ≤ 2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 4 →₀ F2))
    (f : E.Page 2 q ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (a b c : E.Page 4 p)
    (ha : RepresentsOnPage E 4 p
      (e.symm (Finsupp.single 0 1)+e.symm (Finsupp.single 1 1)) a)
    (hb : RepresentsOnPage E 4 p (e.symm (Finsupp.single 2 1)) b)
    (hc : RepresentsOnPage E 4 p (e.symm (Finsupp.single 3 1)) c)
    (d0 : (E.d 2 p ≫ eqToHom (congrArg (E.Page 2) hdeg))
      (e.symm (Finsupp.single 0 1))=f.symm (Finsupp.single 0 1))
    (d1 : (E.d 2 p ≫ eqToHom (congrArg (E.Page 2) hdeg))
      (e.symm (Finsupp.single 1 1))=f.symm (Finsupp.single 0 1))
    (d2 : E.d 2 p (e.symm (Finsupp.single 2 1))=0)
    (d3 : E.d 2 p (e.symm (Finsupp.single 3 1))=0)
    (z : E.Page 4 p) :
    z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c := by
  subst q
  simp only [eqToHom_refl,Category.comp_id] at d0 d1
  exact fourth_frame_of_four_basis hstart e f a b c ha hb hc d0 d1 d2 d3 z

theorem represents_next_nonzero_of_not_incoming
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {q : ℤ × ℤ} (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {x : E.Page 2 (q+E.diffDeg r)} {a : E.Page (r+1) (q+E.diffDeg r)}
    {b : E.Page r (q+E.diffDeg r)}
    (ha : RepresentsOnPage E (r+1) (q+E.diffDeg r) x a)
    (hb : RepresentsOnPage E r (q+E.diffDeg r) x b)
    (havoid : ∀ v : E.Page r q, E.d r q v≠b) : a ≠ 0 := by
  obtain ⟨_,z,hz,hza⟩ := ha
  let D := E.ssData (q+E.diffDeg r)
  let n : ℕ := (r-E.r₀).toNat
  let m : ℕ := (r+1-E.r₀).toNat
  have hnm : n ≤ m := by dsimp only [n,m]; omega
  let i := Subobject.ofLE (D.Z ↑m) (D.Z ↑n) (D.Z_anti (by exact_mod_cast hnm))
  have hb' : RepresentsOnPage E r (q+E.diffDeg r) x (D.pageπ ↑n (i z)) := by
    as_aux_lemma =>
      refine ⟨hr,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE _ _ _ ≫ D.pageπ _) z = x
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz
  have heq : D.pageπ ↑n (i z)=b := represents_unique hb' hb
  let P (k : ℕ) : Prop := ∀ (hk : n ≤ k)
      (w : (Subobject.underlying.obj (D.Z ↑k) : ModuleCat.{v} ℤ)),
    D.pageπ ↑k w = 0 ↔
      (Subobject.ofLE (D.Z ↑k) (D.Z ↑n) (D.Z_anti (by exact_mod_cast hk)) ≫
        D.pageπ ↑n) w ∈ LinearMap.range (E.d r q).hom
  have hP : P (n+1) := by
    intro hk w
    exact next_projection_zero_iff_incoming E r hr0 q w
  have hi : m=n+1 := by dsimp only [m,n]; omega
  have hPm : P m := hi.symm ▸ hP
  intro ha0
  have hm := (hPm hnm z).mp (hza.trans ha0)
  change D.pageπ ↑n (i z) ∈ LinearMap.range (E.d r q).hom at hm
  rw [heq] at hm
  obtain ⟨v,hv⟩ := hm
  exact havoid v hv

theorem represents_next_nonzero_of_not_incoming_at
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p q : ℤ × ℤ} (hdeg : q+E.diffDeg r=p)
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {x : E.Page 2 p} {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (havoid : ∀ v : E.Page r q,
      (E.d r q ≫ eqToHom (congrArg (E.Page r) hdeg)) v≠b) : a≠0 := by
  subst p
  simp only [eqToHom_refl,Category.comp_id] at havoid
  exact represents_next_nonzero_of_not_incoming hr0 hr ha hb havoid

theorem basis_vector_ne_zero
    {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
    (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (i : Fin N) : e.symm (Finsupp.single i 1)≠0 := by
  intro h
  have hh := congrArg (fun a => e a i) h
  exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply,map_zero,
    Finsupp.single_eq_same,Finsupp.zero_apply] using hh)

theorem basis_pair_sum_ne_zero
    {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
    (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (i j : Fin N) (hij : i≠j) :
    e.symm (Finsupp.single i 1)+e.symm (Finsupp.single j 1)≠0 := by
  intro h
  have hh := congrArg (fun a => e a i) h
  simp only [map_add,LinearEquiv.apply_symm_apply,map_zero,Finsupp.add_apply,
    Finsupp.single_eq_same,Finsupp.single_apply,if_neg (Ne.symm hij),add_zero,Finsupp.zero_apply] at hh
  exact one_ne_zero hh

end
/-- Permanent representatives are cycles on page two. This general lemma
is migrated from the backup's Section 7 proof and uses no selected model. -/
theorem isPageCycle_of_permanentCycle
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {x : E.Page 2 p}
    (hbase : E.r₀ ≤ 2) (h : IsPermanentCycle E p x) : IsPageCycle E 2 p x := by
  rcases h with ⟨z, hz⟩
  let SD := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(3 - E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n, m]
    exact_mod_cast (show (2 - E.r₀).toNat ≤ (3 - E.r₀).toNat by omega)
  let z3 := Subobject.ofLE (SD.Z ⊤) (SD.Z m) (SD.Z_anti le_top) z
  have hrep : ReachesPage E 3 p x := by
    refine ⟨SD.pageπ m z3, ?_⟩
    refine ⟨by omega, z3, ?_, rfl⟩
    change SD.pageπ n ((Subobject.ofLE (SD.Z m) (SD.Z n) _) z3) = x
    dsimp only [z3]
    have hcomp := Subobject.ofLE_comp_ofLE (SD.Z ⊤) (SD.Z m) (SD.Z n)
      (SD.Z_anti le_top) (SD.Z_anti hnm)
    have hcomp' :
        (Subobject.ofLE (SD.Z ⊤) (SD.Z m) (SD.Z_anti le_top) ≫
          Subobject.ofLE (SD.Z m) (SD.Z n) (SD.Z_anti hnm)) ≫ SD.pageπ n =
        Subobject.ofLE (SD.Z ⊤) (SD.Z n) (SD.Z_anti le_top) ≫ SD.pageπ n := by
      exact congrArg (fun f => f ≫ SD.pageπ n) hcomp
    have hz' := congrArg (fun f => f z) hcomp'
    exact hz'.trans hz
  have hself : RepresentsOnPage E 2 p x x :=
    KIP126.SpectralSequence.FinitePageCalculus.represents_two_self x
  exact KIP126.SpectralSequence.FinitePageCalculus.represents_d_zero_of_later
    (E := E) (p := p) (x := x) (r := 2) (t := 3) hbase (by omega) hself hrep

theorem isPageCycle_of_nonzeroSurvival
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {x : E.Page 2 p}
    (hbase : E.r₀ ≤ 2) (h : NonzeroSurvival E p x) : IsPageCycle E 2 p x := by
  rcases h with ⟨z, hz, _⟩
  exact isPageCycle_of_permanentCycle hbase ⟨z, hz⟩

end KIP126.SpectralSequence.FinitePageCalculus
