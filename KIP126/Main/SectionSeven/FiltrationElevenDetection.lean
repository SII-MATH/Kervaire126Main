module

public import Batteries.Tactic.OpenPrivate
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import Init.Data.String.Lemmas.Splits
public import KIP126.Def.SpectralSequence.FilteredComplex.Crossing.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.Synthetic.QuotientTower.Proofs
public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Data
public import KIP126.Def.StableHomotopy.Toda.Law.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Main.Computation.SphereAndCofiber.Consequences
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.Classes.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.Predicates

-- The CSV coordinate calculations use the defining string and list equations.
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

@[expose] public section


namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}

private theorem weaky0_represents_unique {a b : E.Page r p}
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

private theorem weaky0_represents_smul {a : E.Page r p} (ha : RepresentsOnPage E r p x a) (c : R) :
    RepresentsOnPage E r p (c • x) (c • a) := by
  obtain ⟨hr, z, hz, hza⟩ := ha
  refine ⟨hr, c • z, ?_, ?_⟩ <;> simp only [map_smul, hz, hza]

private theorem weaky0_represents_d_zero_of_later {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
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
  rw [weaky0_represents_unique ha hrep]
  change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
  rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
  refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z, ?_⟩
  change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
    ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  rfl

end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky0_next_projection_zero_iff_incoming
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
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
end KIP126.SpectralSequence

namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
private theorem weaky0_page_generated_from_representatives
    {E : SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r)
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
  refine ⟨c, weaky0_represents_unique hxa ?_⟩
  have hh := hsum Finset.univ
  simpa only [hx] using hh
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky0_represents_before
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
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
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky0_next_page_two_of_kernel
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (v : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat R))
    (hcases : ∀ a : E.Page r p, E.d r p a = 0 → a = 0 ∨
      a = (Subobject.ofLE _ _ ((E.ssData p).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData p).pageπ ↑(r-E.r₀).toNat) v) :
    ∀ a : ((E.ssData p).page ↑((r-E.r₀).toNat+1) : ModuleCat R),
      a = 0 ∨ a = (E.ssData p).pageπ ↑((r-E.r₀).toNat+1) v := by
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let down := i ≫ D.pageπ ↑n
  have hzero (z : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat R))
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
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky0_represents_next_nonzero_of_incoming_zero
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
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
  rw [weaky0_represents_unique hb hb']
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mpr
  have hm := (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) z).mp (hza.trans ha0)
  rw [hB] at hm
  change (i ≫ (D.Z n).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]
end KIP126.SpectralSequence


namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}

private theorem weaky0_differential_target_later_zero
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

end KIP126.SpectralSequence

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

open KIP126.Algebra PageRepresentatives
private theorem weaky0_boundary_of_zero_representative
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

private theorem weaky0_middle_add {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x+y) (a+b) := by
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩

private theorem weaky0_middle_if {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
    (c : F2) (h : RepresentsOnPage E r p x a) :
    RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
  split
  · exact RepresentsOnPage.zero h.1
  · exact h

private theorem weaky0_middle_expand {N : ℕ} (f : Fin N →₀ F2) :
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

private theorem weaky0_middle_rep2 {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r)
    (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
  obtain ⟨b,hb⟩ := weaky0_represents_before (by decide : (2:ℤ)≤2) hr ha
  rw [←hb.eq_on_page_two] at hb
  exact hb

private theorem weaky0_nu9_af12_kernel (I : AdamsComputationTheorems D L G)
    (x : Page D .sphere 12 137)
    (dx : (sequence D .sphere).d 2 (12,137) x = 0) :
    RepresentsOnPage (sequence D .sphere) 4 (12,137) x 0 := by
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.interpretation.basis .sphere 10 136 0)) ((I.interpretation.basis .sphere 12 137 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
      unfold Raw.claims
      iterate 260 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,136) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
      unfold Raw.claims
      iterate 234 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h307 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 0) + (I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
      unfold Raw.claims
      iterate 307 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h308 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 1)) ((I.interpretation.basis .sphere 14 138 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
      unfold Raw.claims
      iterate 308 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h309 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 0)) ((I.interpretation.basis .sphere 14 138 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
      unfold Raw.claims
      iterate 309 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 201 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    unfold Raw.degrees
    iterate 216 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 138 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 14 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 14 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 14 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 14 138 4 := hf 4
  have hz2 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 2) 0 :=
    weaky0_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
  have d2 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 2)=0 :=
    weaky0_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky0_middle_rep2 (by decide) hz2) ⟨0,hz2⟩
  have hz3 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 3) 0 :=
    weaky0_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
  have d3 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 3)=0 :=
    weaky0_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky0_middle_rep2 (by decide) hz3) ⟨0,hz3⟩
  have hz4 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 4) 0 :=
    weaky0_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
  have d4 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 4)=0 :=
    weaky0_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky0_middle_rep2 (by decide) hz4) ⟨0,hz4⟩
  have d0 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 0)=I.interpretation.basis .sphere 14 138 3 := h309.eq_on_page_two.2
  have d1 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 1)=I.interpretation.basis .sphere 14 138 4 := h308.eq_on_page_two.2
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (weaky0_middle_expand (e x))
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
  have hh := weaky0_middle_add (weaky0_middle_if (c 2) hz2) (weaky0_middle_add (weaky0_middle_if (c 3) hz3) (weaky0_middle_if (c 4) hz4))
  simpa only [ite_self,zero_add] using hh

private theorem weaky0_nu9_af13_cosets (I : AdamsComputationTheorems D L G) :
    I.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
    ∀ x : Page D .sphere 13 138,
      x ∈ boundaries H SphereSpectrum 4 (13,138) ∨
      x - I.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 4 (13,138) := by
  let E := sequence D .sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
      unfold Raw.claims
      iterate 231 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
      unfold Raw.claims
      iterate 232 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
      unfold Raw.claims
      iterate 288 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
      unfold Raw.claims
      iterate 289 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((I.interpretation.basis .sphere 13 138 1)) ((I.interpretation.basis .sphere 16 140 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
      unfold Raw.claims
      iterate 329 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (13,138) (16,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd

  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 209 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at he

  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := he 4

  constructor
  · obtain ⟨_, a, b, ha, hb, hd⟩ := h329
    exact ((isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,138)
      (I.interpretation.basis .sphere 13 138 1)).mpr ⟨a,ha⟩).2
  · intro x
    let P := boundaries H SphereSpectrum 4 (13,138)
    have hb0 : I.interpretation.basis .sphere 13 138 0 ∈ P :=
      weaky0_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky0_differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h231)
    have hb2 : I.interpretation.basis .sphere 13 138 2 ∈ P :=
      weaky0_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky0_differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h232)
    have hb3 : I.interpretation.basis .sphere 13 138 3 ∈ P :=
      weaky0_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky0_differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h288)
    have hb4 : I.interpretation.basis .sphere 13 138 4 ∈ P :=
      weaky0_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky0_differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h289)
    have hif (c : F2) {a : Page D .sphere 13 138} (h : a ∈ P) :
        (if c=0 then 0 else a) ∈ P := by
      split
      · exact P.zero_mem
      · exact h
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (weaky0_middle_expand (e x))
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
      change x - I.interpretation.basis .sphere 13 138 1 ∈ P
      rw [hcoef]
      simp only [hc,ite_false]
      convert hm using 1 <;> first | rfl | abel

private theorem weaky0_nu9_af12_cycles_boundary (I : AdamsComputationTheorems D L G) :
    cycles H SphereSpectrum 2 (12,137) ≤ boundaries H SphereSpectrum 3 (12,137) := by
  intro x hx
  obtain ⟨a,ha⟩ := (isCycle_iff_represents H SphereSpectrum 3 (by decide) (12,137) x).mp
    ⟨by decide, by simpa using hx⟩
  have hself := weaky0_middle_rep2 (E:=sequence D .sphere) (r:=3) (p:=(12,137)) (by decide : (2:ℤ)≤3) ha
  have hd : (sequence D .sphere).d 2 (12,137) x=0 :=
    weaky0_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      hself ⟨a,ha⟩
  exact weaky0_boundary_of_zero_representative (r:=4) (p:=(12,137)) (weaky0_nu9_af12_kernel I x hd)

private theorem weaky0_nu9_af12_cycle_quotient_zero (I : AdamsComputationTheorems D L G) :
    Subsingleton (CycleQuotient H SphereSpectrum 2 8 (12,137)) := by
  have hz (x : CycleQuotient H SphereSpectrum 2 8 (12,137)) : x=0 := by
    obtain ⟨x⟩ := x
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum (12,137) (by decide : (3:ℤ)≤8)
        (weaky0_nu9_af12_cycles_boundary I x.property))
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩

private theorem weaky0_nu9_af13_cosets_nine (I : AdamsComputationTheorems D L G) :
    I.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
    ∀ x : Page D .sphere 13 138,
      x ∈ boundaries H SphereSpectrum 9 (13,138) ∨
      x - I.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 9 (13,138) := by
  obtain ⟨hc,h⟩ := weaky0_nu9_af13_cosets I
  refine ⟨hc,fun x=>?_⟩
  rcases h x with hx | hx
  · exact Or.inl (boundaries_monotone H SphereSpectrum (13,138) (by decide : (4:ℤ)≤9) hx)
  · exact Or.inr (boundaries_monotone H SphereSpectrum (13,138) (by decide : (4:ℤ)≤9) hx)

end KIP126.Computation.SphereAndCofiber

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2 KIP126.Algebra PageRepresentatives
open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem weaky0_af13_basis_not_cycle (I : AdamsComputationTheorems D L G) :
    I.interpretation.basis .sphere 13 138 1 ∉ cycles H SphereSpectrum 3 (13,138) := by
  let E := sequence D .sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
      unfold Raw.claims
      iterate 231 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
      unfold Raw.claims
      iterate 232 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
      unfold Raw.claims
      iterate 288 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
      unfold Raw.claims
      iterate 289 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((I.interpretation.basis .sphere 13 138 1)) ((I.interpretation.basis .sphere 16 140 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
      unfold Raw.claims
      iterate 329 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (13,138) (16,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h314 : HasDifferential E 2 (12,138) (14,139)
      ((I.interpretation.basis .sphere 12 138 1)) ((I.interpretation.basis .sphere 14 139 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3017⟩ (by
      unfold Raw.claims
      iterate 314 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,138) (14,139) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h343 : HasDifferential E 2 (14,139) (16,140)
      ((I.interpretation.basis .sphere 14 139 0)) ((I.interpretation.basis .sphere 16 140 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
      unfold Raw.claims
      iterate 343 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,139) (16,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
    have hh := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
      unfold Raw.claims
      iterate 342 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 209 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    unfold Raw.degrees
    iterate 217 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
    unfold Raw.degrees
    iterate 231 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 140 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 139 2 := hf 2
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 16 140 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 16 140 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 16 140 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 16 140 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 16 140 4 := hg 4
  have df0 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 0)=I.interpretation.basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have df1 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 1)=0 := by
    obtain ⟨x,hx⟩ := h342
    exact weaky0_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000)
      (weaky0_middle_rep2 (by decide) hx) ⟨x,hx⟩
  have df2 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(12,138)) ⟨_,h314.eq_on_page_two.2⟩
  have incoming (x : E.Page 2 (14,139)) : g (E.d 2 (14,139) x) 1=0 := by
    have all (a : Fin 3 →₀ F2) : g (E.d 2 (14,139) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (14,139) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [df0,df1,df2,map_zero,Finsupp.zero_apply,←hg2,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (f x)
  obtain ⟨_,b1,t,hb1,ht,db1⟩ := h329
  have db1' : E.d 3 (13,138) b1=t := db1
  have tn : t≠0 := by
    intro ht0
    obtain ⟨_,z,hz,hzt⟩ := ht
    have hh := (weaky0_next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (14,139) z).mp (hzt.trans ht0)
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z ∈ LinearMap.range (E.d 2 (14,139)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z = I.interpretation.basis .sphere 16 140 1 at hz
    rw [hz] at hh
    obtain ⟨u,hu⟩ := hh
    have hh := incoming u
    rw [hu,←hg1,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  intro hc
  obtain ⟨b4,hb4⟩ := (isCycle_iff_represents H SphereSpectrum 4 (by decide) (13,138)
    (I.interpretation.basis .sphere 13 138 1)).mp ⟨by decide,hc⟩
  exact tn (db1'.symm.trans (weaky0_represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb1 ⟨b4,hb4⟩))

private theorem weaky0_af13_cycles_boundary (I : AdamsComputationTheorems D L G) :
    cycles H SphereSpectrum 3 (13,138) ≤ boundaries H SphereSpectrum 4 (13,138) := by
  intro x hx
  rcases (weaky0_nu9_af13_cosets I).2 x with h|h
  · exact h
  · exfalso
    apply weaky0_af13_basis_not_cycle I
    have hh := (boundaries_le_cycles H SphereSpectrum (13,138) 4 3) h
    simpa only [sub_sub_cancel] using (cycles H SphereSpectrum 3 (13,138)).sub_mem hx hh

private theorem weaky0_af12_quotient_zero (I : AdamsComputationTheorems D L G) :
    Subsingleton (CycleQuotient H SphereSpectrum 4 6 (12,137)) := by
  have hz (x : CycleQuotient H SphereSpectrum 4 6 (12,137)) : x=0 := by
    obtain ⟨x⟩ := x
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum (12,137) (by decide : (3:ℤ)≤6)
        (weaky0_nu9_af12_cycles_boundary I
          (cycles_antitone H SphereSpectrum (12,137) (by decide : (2:ℤ)≤4) x.property)))
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩

private theorem weaky0_af13_quotient_zero (I : AdamsComputationTheorems D L G) :
    Subsingleton (CycleQuotient H SphereSpectrum 3 7 (13,138)) := by
  have hz (x : CycleQuotient H SphereSpectrum 3 7 (13,138)) : x=0 := by
    obtain ⟨x⟩ := x
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum (13,138) (by decide : (4:ℤ)≤7)
        (weaky0_af13_cycles_boundary I x.property))
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
private theorem weaky0_finite_sphere_zero_of_classical_quotient
    (BHS : EInftyComparison D) (q : ℕ) (hq : 0<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<q)
    (hc : Subsingleton (CycleQuotient H SphereSpectrum ((q:ℤ)-t+w) (1+t-w) (s,t))) :
    IsZero (((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,w)).eInfty) := by
  let e := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) w hw
  haveI := hc
  haveI : Subsingleton (((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
  let f := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom q)).eInftyMap (s,t,w)
  let g := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.inv q)).eInftyMap (s,t,w)
  have hfg : g ≫ f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem weaky0_weight132_filtration_twelve_fourteen
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D)
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
  apply (D.quotientConvergence 9 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
    12 14 125 132 (by decide)
  intro j hj hj'
  have hcases : j=12 ∨ j=13 := by omega
  rcases hcases with rfl|rfl
  · exact weaky0_finite_sphere_zero_of_classical_quotient BHS 9 (by decide) 12 137 132
      (by norm_num) (weaky0_af12_quotient_zero I)
  · exact weaky0_finite_sphere_zero_of_classical_quotient BHS 9 (by decide) 13 138 132
      (by norm_num) (weaky0_af13_quotient_zero I)

private theorem weaky0_representatives_differ_in_fourteen
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D)
    (y z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hy : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y)
    (hz : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) z) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (y-z) := by
  apply (weaky0_weight132_filtration_twelve_fourteen I BHS (y-z)).mp
  exact detects_sub_filtration (D.quotientConvergence 9 (by decide))
    (11,136,132) hy.1 hz.1
end KIP126.Computation.SphereAndCofiber

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2 KIP126.Algebra PageRepresentatives
open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem weaky0_family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
private theorem weaky0_family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  rw [weaky0_family_map_data,weaky0_family_map_data,weaky0_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
private theorem weaky0_family_infinity_representative_map
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
  · rw [weaky0_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])
private theorem weaky0_sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (weaky0_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (weaky0_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (weaky0_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel

private theorem weaky0_finite_sphere_infinity_label_exists
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
    ∃ x : E2 H SphereSpectrum s t,
      HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D.quotientLabel q s t k x) e := by
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have heq : (D.family.functor.map f).eInftyMap (s,t,t-k)
      ((D.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
    change ((D.family.functor.map g).eInftyMap (s,t,t-k) ≫
      (D.family.functor.map f).eInftyMap (s,t,t-k)) e=e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  obtain ⟨c,hc⟩ := Quotient.exists_rep (P ((D.family.functor.map g).eInftyMap (s,t,t-k) e))
  have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hc.symm
  have hl : familyPageMap D.family f 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k c.val)=D.quotientLabel q s t k c.val := by
    rw [←weaky0_sphere_quotient_label_to_nu (D:=D) q k s t c.val]
    calc
      _ = familyPageMap D.family (g≫f) 2 (s,t,t-k) (D.quotientLabel q s t k c.val) :=
        ConcreteCategory.congr_hom (weaky0_family_page_comp (D:=D) g f 2 (s,t,t-k)) _
      _ = D.quotientLabel q s t k c.val := by
        rw [hgf,weaky0_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
          (s,t,t-k) ↑(2-2:ℤ).toNat) _
  have h := weaky0_family_infinity_representative_map f (s,t,t-k) _ _ hn
  rw [hl,heq] at h
  exact ⟨c.val,h⟩

private theorem weaky0_finite_sphere_filtration_has_label
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    ∃ x : E2 H SphereSpectrum s t,
      Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (XModLambdaN (S_0_0 : Syn) q)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (t-s,t-k)))
      (F.F s (t-s,t-k)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let gr := F.toAssociatedGraded s (t-s,t-k) a'
  let e := ((D.quotientConvergence q hq).identification (s,t,t-k)).inv gr
  have he : ((D.quotientConvergence q hq).identification (s,t,t-k)).hom e=gr :=
    ConcreteCategory.congr_hom ((D.quotientConvergence q hq).identification (s,t,t-k)).inv_hom_id gr
  obtain ⟨x,hx⟩ := weaky0_finite_sphere_infinity_label_exists BHS q k hq hkq s t e
  exact ⟨x,e,hx,a',ha',he⟩

private theorem weaky0_h0_increases_fourteen
    (BHS : EInftyComparison D) (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hd : Detects D.sphereConvergence (1,1,1)
      (D.sphereE2 1 1 0 (Sphere.Internal.hi H M 0)) h0)
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereAction h0 a) := by
  obtain ⟨x,hx⟩ := weaky0_finite_sphere_filtration_has_label BHS 9 7 (by decide) (by decide) 14 139 a ha
  have hp := ab.finite_action 9 (by decide) 1 1 14 139 0 7
    (Sphere.Internal.hi H M 0) x h0 a hd hx
  obtain ⟨e,he,b,hb,_⟩ := hp
  have hm : (sphereAction h0 a) ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) 9) (125,133)))
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (XModLambdaN (S_0_0 : Syn) 9)).F 15 (125,133)) := ⟨b,hb⟩
  simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast,Int.reduceAdd] using hm

private theorem weaky0_h0_representative_difference
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D) (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hd : Detects D.sphereConvergence (1,1,1)
      (D.sphereE2 1 1 0 (Sphere.Internal.hi H M 0)) h0)
    (y z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hy : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y)
    (hz : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) z) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
      (sphereAction h0 y - sphereAction h0 z) := by
  simpa only [sphereAction,Preadditive.comp_sub] using
    weaky0_h0_increases_fourteen BHS A ab h0 hd (y-z)
      (weaky0_representatives_differ_in_fourteen I BHS y z hy hz)
private theorem weaky0_detects_of_difference
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

private theorem weaky0_h0_detection_independent
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D) (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hd : Detects D.sphereConvergence (1,1,1)
      (D.sphereE2 1 1 0 (Sphere.Internal.hi H M 0)) h0)
    (y z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hy : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y)
    (hz : FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) z)
    (T : E2 H SphereSpectrum 14 139)
    (ht : FiniteDetected D 9 (by decide) 14 139 6 T (sphereAction h0 z)) :
    FiniteDetected D 9 (by decide) 14 139 6 T (sphereAction h0 y) := by
  refine ⟨?_,ht.2⟩
  apply weaky0_detects_of_difference (D.quotientConvergence 9 (by decide)) (14,139,133) ht.1
  exact weaky0_h0_representative_difference I BHS A ab h0 hd y z hy hz

private theorem weaky0_h0_source_detected (η : BiHom 1 2 (S_0_0 : Syn))
    (T : TodaRelations D η) :
    Detects D.sphereConvergence (1,1,1)
      (D.sphereE2 1 1 0 (Sphere.Internal.hi H M 0)) T.h0 := by
  have hz : lambdaMultiply 0 T.h0=T.h0 := by
    have hc := D.shiftCoherence.right_unit (0,1) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : Syn) := by
      change (biShiftAddIso (0,1) (0,0) (0,1) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn) ≫ T.h0=T.h0
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have h := D.comparisonCompatible.homotopy_lambda 1 1 0 T.h0
  rw [T.h0_label,hz] at h
  exact h

private theorem weaky0_h0_detection_from_one
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D) (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (η : BiHom 1 2 (S_0_0 : Syn)) (low : TodaRelations D η)
    (T : E2 H SphereSpectrum 14 139)
    (hone : ∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9),
      FiniteDetected D 9 (by decide) 11 136 4
        (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) z ∧
      FiniteDetected D 9 (by decide) 14 139 6 T (sphereAction low.h0 z)) :
    ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9),
      FiniteDetected D 9 (by decide) 11 136 4
        (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y →
      FiniteDetected D 9 (by decide) 14 139 6 T (sphereAction low.h0 y) := by
  obtain ⟨z,hz,ht⟩ := hone
  intro y hy
  exact weaky0_h0_detection_independent I BHS A ab low.h0
    (weaky0_h0_source_detected η low) y z hy hz T ht
end KIP126.Computation.SphereAndCofiber

namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}

private theorem weaky1_represents_unique {a b : E.Page r p}
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

private theorem weaky1_represents_smul {a : E.Page r p} (ha : RepresentsOnPage E r p x a) (c : R) :
    RepresentsOnPage E r p (c • x) (c • a) := by
  obtain ⟨hr, z, hz, hza⟩ := ha
  refine ⟨hr, c • z, ?_, ?_⟩ <;> simp only [map_smul, hz, hza]

private theorem weaky1_represents_d_zero_of_later {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
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
  rw [weaky1_represents_unique ha hrep]
  change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
  rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
  refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z, ?_⟩
  change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
    ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  rfl

end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky1_next_projection_zero_iff_incoming
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
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
end KIP126.SpectralSequence

namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
private theorem weaky1_page_generated_from_representatives
    {E : SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r)
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
  refine ⟨c, weaky1_represents_unique hxa ?_⟩
  have hh := hsum Finset.univ
  simpa only [hx] using hh
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky1_represents_before
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
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
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky1_next_page_two_of_kernel
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (v : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat R))
    (hcases : ∀ a : E.Page r p, E.d r p a = 0 → a = 0 ∨
      a = (Subobject.ofLE _ _ ((E.ssData p).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData p).pageπ ↑(r-E.r₀).toNat) v) :
    ∀ a : ((E.ssData p).page ↑((r-E.r₀).toNat+1) : ModuleCat R),
      a = 0 ∨ a = (E.ssData p).pageπ ↑((r-E.r₀).toNat+1) v := by
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let down := i ≫ D.pageπ ↑n
  have hzero (z : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat R))
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
end KIP126.SpectralSequence
namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
private theorem weaky1_represents_next_nonzero_of_incoming_zero
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
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
  rw [weaky1_represents_unique hb hb']
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mpr
  have hm := (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) z).mp (hza.trans ha0)
  rw [hB] at hm
  change (i ≫ (D.Z n).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]
end KIP126.SpectralSequence


namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}

private theorem weaky1_differential_target_later_zero
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

end KIP126.SpectralSequence

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

open KIP126.Algebra PageRepresentatives
private theorem weaky1_boundary_of_zero_representative
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

private theorem weaky1_middle_add {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x+y) (a+b) := by
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩

private theorem weaky1_middle_if {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
    (c : F2) (h : RepresentsOnPage E r p x a) :
    RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
  split
  · exact RepresentsOnPage.zero h.1
  · exact h

private theorem weaky1_middle_expand {N : ℕ} (f : Fin N →₀ F2) :
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

private theorem weaky1_middle_rep2 {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r)
    (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
  obtain ⟨b,hb⟩ := weaky1_represents_before (by decide : (2:ℤ)≤2) hr ha
  rw [←hb.eq_on_page_two] at hb
  exact hb

private theorem weaky1_nu9_af12_kernel (I : AdamsComputationTheorems D L G)
    (x : Page D .sphere 12 137)
    (dx : (sequence D .sphere).d 2 (12,137) x = 0) :
    RepresentsOnPage (sequence D .sphere) 4 (12,137) x 0 := by
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.interpretation.basis .sphere 10 136 0)) ((I.interpretation.basis .sphere 12 137 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
      unfold Raw.claims
      iterate 260 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,136) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
      unfold Raw.claims
      iterate 234 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h307 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 0) + (I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
      unfold Raw.claims
      iterate 307 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h308 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 1)) ((I.interpretation.basis .sphere 14 138 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
      unfold Raw.claims
      iterate 308 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h309 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 0)) ((I.interpretation.basis .sphere 14 138 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
      unfold Raw.claims
      iterate 309 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 201 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    unfold Raw.degrees
    iterate 216 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 138 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 14 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 14 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 14 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 14 138 4 := hf 4
  have hz2 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 2) 0 :=
    weaky1_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
  have d2 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 2)=0 :=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky1_middle_rep2 (by decide) hz2) ⟨0,hz2⟩
  have hz3 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 3) 0 :=
    weaky1_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
  have d3 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 3)=0 :=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky1_middle_rep2 (by decide) hz3) ⟨0,hz3⟩
  have hz4 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 4) 0 :=
    weaky1_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
  have d4 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 4)=0 :=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (weaky1_middle_rep2 (by decide) hz4) ⟨0,hz4⟩
  have d0 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 0)=I.interpretation.basis .sphere 14 138 3 := h309.eq_on_page_two.2
  have d1 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 1)=I.interpretation.basis .sphere 14 138 4 := h308.eq_on_page_two.2
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (weaky1_middle_expand (e x))
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
  have hh := weaky1_middle_add (weaky1_middle_if (c 2) hz2) (weaky1_middle_add (weaky1_middle_if (c 3) hz3) (weaky1_middle_if (c 4) hz4))
  simpa only [ite_self,zero_add] using hh

private theorem weaky1_nu9_af13_cosets (I : AdamsComputationTheorems D L G) :
    I.interpretation.basis .sphere 13 138 1 ∈ cycles H SphereSpectrum 2 (13,138) ∧
    ∀ x : Page D .sphere 13 138,
      x ∈ boundaries H SphereSpectrum 4 (13,138) ∨
      x - I.interpretation.basis .sphere 13 138 1 ∈ boundaries H SphereSpectrum 4 (13,138) := by
  let E := sequence D .sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
      unfold Raw.claims
      iterate 231 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
      unfold Raw.claims
      iterate 232 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
      unfold Raw.claims
      iterate 288 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
      unfold Raw.claims
      iterate 289 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((I.interpretation.basis .sphere 13 138 1)) ((I.interpretation.basis .sphere 16 140 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
      unfold Raw.claims
      iterate 329 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (13,138) (16,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd

  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 209 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at he

  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := he 4

  constructor
  · obtain ⟨_, a, b, ha, hb, hd⟩ := h329
    exact ((isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,138)
      (I.interpretation.basis .sphere 13 138 1)).mpr ⟨a,ha⟩).2
  · intro x
    let P := boundaries H SphereSpectrum 4 (13,138)
    have hb0 : I.interpretation.basis .sphere 13 138 0 ∈ P :=
      weaky1_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky1_differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h231)
    have hb2 : I.interpretation.basis .sphere 13 138 2 ∈ P :=
      weaky1_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky1_differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h232)
    have hb3 : I.interpretation.basis .sphere 13 138 3 ∈ P :=
      weaky1_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky1_differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h288)
    have hb4 : I.interpretation.basis .sphere 13 138 4 ∈ P :=
      weaky1_boundary_of_zero_representative (r:=5) (p:=(13,138))
        (weaky1_differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h289)
    have hif (c : F2) {a : Page D .sphere 13 138} (h : a ∈ P) :
        (if c=0 then 0 else a) ∈ P := by
      split
      · exact P.zero_mem
      · exact h
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (weaky1_middle_expand (e x))
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
      change x - I.interpretation.basis .sphere 13 138 1 ∈ P
      rw [hcoef]
      simp only [hc,ite_false]
      convert hm using 1 <;> first | rfl | abel


private theorem weaky1_main_af15_incoming2_zero (I:AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 2 (13,138)=0 := by
  let E:=sequence D .sphere
  ext x
  have hc:x∈cycles H SphereSpectrum 2 (13,138) := by
    obtain ⟨hb,hx⟩:=weaky1_nu9_af13_cosets I
    rcases hx x with hx|hx
    · exact boundaries_le_cycles H SphereSpectrum (13,138) 4 2 hx
    · have hsum := (cycles H SphereSpectrum 2 (13,138)).add_mem
        (boundaries_le_cycles H SphereSpectrum (13,138) 4 2 hx) hb
      simpa only [sub_add_cancel] using hsum
  obtain ⟨a,ha⟩:ReachesPage E 3 (13,138) x :=
    (isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,138) x).mp ⟨by decide,hc⟩
  exact weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
    (weaky1_middle_rep2 (by decide) ha) ⟨a,ha⟩

private theorem weaky1_main_af15_incoming3_zero (I:AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 3 (12,137)=0 := by
  let E:=sequence D .sphere
  ext a
  let P:=E.ssData (12,137)
  haveI:Epi (P.pageπ 1):=inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩:=(ModuleCat.epi_iff_surjective (P.pageπ 1)).mp inferInstance a
  let x:E.Page 2 (12,137):=(Subobject.ofLE _ _ (P.Z_anti (by decide : (0:WithTop ℕ)≤1))≫P.pageπ 0) z
  have hx:RepresentsOnPage E 3 (12,137) x a:=⟨by decide,z,rfl,hz⟩
  have hd:E.d 2 (12,137) x=0:=weaky1_represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) hx) ⟨a,hx⟩
  exact weaky1_represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hx
    ⟨0,weaky1_nu9_af12_kernel I x hd⟩

private theorem weaky1_main_af11_d4_target_nonzero (I:AdamsComputationTheorems D L G)
    (a:(sequence D .sphere).Page 4 (15,139))
    (ha:RepresentsOnPage (sequence D .sphere) 4 (15,139)
      (I.interpretation.basis .sphere 15 139 0) a):a≠0 := by
  let E:=sequence D .sphere
  obtain ⟨e,he⟩:=I.basis ⟨.sphere,15,139,["448,1","3,2,287,1","0,1,440,1","0,1,439,1"]⟩ (by
    unfold Raw.degrees
    iterate 223 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,139)≃ₗ[ℤ](Fin 4→₀F2) at e
  change ∀i:Fin 4,e.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 15 139 i.val at he
  have hn:I.interpretation.basis .sphere 15 139 0≠0 := by
    erw [←he 0]
    intro hz
    have hh:=congrArg (fun x=>e x 0) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨a3,ha3⟩:=weaky1_represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
  have hn3:a3≠0:=weaky1_represents_next_nonzero_of_incoming_zero
    (E:=E) (r:=2) (p:=(15,139)) (by change (2:ℤ)≤2; omega) (by decide)
    (weaky1_main_af15_incoming2_zero I) ha3 (weaky1_middle_rep2 (by decide) ha3) hn
  exact weaky1_represents_next_nonzero_of_incoming_zero
    (E:=E) (r:=3) (p:=(15,139)) (by change (2:ℤ)≤3; omega) (by decide)
    (weaky1_main_af15_incoming3_zero I) ha ha3 hn3

private theorem weaky1_main_y_finite_cosets (I:AdamsComputationTheorems D L G)
    (x:Page D .sphere 11 136) (hx:x∈cycles H SphereSpectrum 5 (11,136)) :
    x∈boundaries H SphereSpectrum 5 (11,136) ∨
    x-I.interpretation.basis .sphere 11 136 3∈boundaries H SphereSpectrum 5 (11,136) := by
  let E:=sequence D .sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      (I.interpretation.basis .sphere 8 134 3) (I.interpretation.basis .sphere 11 136 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
      unfold Raw.claims
      iterate 279 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      (I.interpretation.basis .sphere 8 134 2) (I.interpretation.basis .sphere 11 136 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
      unfold Raw.claims
      iterate 280 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      (I.interpretation.basis .sphere 11 136 0) (I.interpretation.basis .sphere 15 139 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
      unfold Raw.claims
      iterate 282 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
      unfold Raw.claims
      iterate 283 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h281 : ReachesPage E 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
      unfold Raw.claims
      iterate 281 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 5 (11,136) x at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    simpa only [add_assoc] using hd
  have h281 : ReachesPage E 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := by
    have hh := I.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
      unfold Raw.claims
      iterate 281 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    unfold Raw.degrees
    iterate 192 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1)=I.interpretation.basis .sphere 11 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1)=I.interpretation.basis .sphere 11 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1)=I.interpretation.basis .sphere 11 136 2 := he 2
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1)=I.interpretation.basis .sphere 11 136 4 := he 4
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1)=I.interpretation.basis .sphere 11 136 3 := he 3

  obtain ⟨_,a0,b0,ha0,hb0,hd0⟩:=h282
  obtain ⟨y5,hy5⟩:=h281
  obtain ⟨y4,hy4⟩:=weaky1_represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hbne:b0≠0:=weaky1_main_af11_d4_target_nonzero I b0 hb0
  have hy_d4:E.d 4 (11,136) y4=0:=weaky1_represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide) hy4 ⟨y5,hy5⟩
  have h1:RepresentsOnPage E 4 (11,136) (I.interpretation.basis .sphere 11 136 1) 0:=
    weaky1_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h279
  have h2:RepresentsOnPage E 4 (11,136) (I.interpretation.basis .sphere 11 136 2) 0:=
    weaky1_differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h280
  have d0:E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 0)=0:=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) ha0) ⟨a0,ha0⟩
  have d1:E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 1)=0:=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) h1) ⟨0,h1⟩
  have d2:E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 2)=0:=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) h2) ⟨0,h2⟩
  have d3:E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 3)=0:=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) hy4) ⟨y4,hy4⟩
  have d4:E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 4)=I.interpretation.basis .sphere 13 137 3:=h283.eq_on_page_two.2
  have hd4ne:I.interpretation.basis .sphere 13 137 3≠0 := by
    obtain ⟨f,hf⟩:=I.basis ⟨.sphere,13,137,["76,1,82,1","9,1,251,1","7,1,275,1","0,5,367,1"]⟩ (by
      unfold Raw.degrees
      iterate 208 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (13,137)≃ₗ[ℤ](Fin 4→₀F2) at f
    change ∀i:Fin 4,f.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 13 137 i.val at hf
    erw [←hf 3]
    intro hz
    have hh:=congrArg (fun x=>f x 3) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨a6,ha6⟩:ReachesPage E 6 (11,136) x:=
    (isCycle_iff_represents H SphereSpectrum 6 (by decide) (11,136) x).mp ⟨by decide,hx⟩
  have dx:E.d 2 (11,136) x=0:=weaky1_represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide) (weaky1_middle_rep2 (by decide) ha6) ⟨a6,ha6⟩
  let c:Fin 5→F2:=e x
  have hcoef:=congrArg e.symm (weaky1_middle_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have c4:c 4=0 := by
    have hd:=congrArg (E.d 2 (11,136)) hcoef
    rw [dx] at hd
    by_contra h4
    simp only [h4,ite_false,map_add,apply_ite,map_zero,d0,d1,d2,d3,d4,ite_self,zero_add] at hd
    exact hd4ne hd.symm
  simp only [c4,ite_true,add_zero] at hcoef
  have hrep:RepresentsOnPage E 4 (11,136) x
      ((if c 0=0 then 0 else a0)+(if c 3=0 then 0 else y4)) := by
    rw [hcoef]
    simpa only [ite_self,zero_add] using
      weaky1_middle_add (weaky1_middle_if (c 0) ha0)
        (weaky1_middle_add (weaky1_middle_if (c 1) h1) (weaky1_middle_add (weaky1_middle_if (c 2) h2) (weaky1_middle_if (c 3) hy4)))
  have hd:E.d 4 (11,136) ((if c 0=0 then 0 else a0)+(if c 3=0 then 0 else y4))=0:=
    weaky1_represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hrep ⟨a6,ha6⟩
  have c0:c 0=0 := by
    by_contra h0
    simp only [h0,ite_false,map_add,apply_ite,hy_d4,ite_self,add_zero] at hd
    exact hbne (hd0.symm.trans hd)
  simp only [c0,ite_true,zero_add] at hrep
  by_cases h3:c 3=0
  · left
    simp only [h3,ite_true] at hrep
    exact boundaries_monotone H SphereSpectrum (11,136) (by decide : (3:ℤ)≤5)
      (weaky1_boundary_of_zero_representative (H:=H) (r:=4) (p:=(11,136)) hrep)
  · right
    simp only [h3,ite_false] at hrep
    have hsub:RepresentsOnPage E 4 (11,136) (x-I.interpretation.basis .sphere 11 136 3) 0 := by
      obtain ⟨hr,z,hz,hza⟩:=hrep
      obtain ⟨_,w,hw,hwa⟩:=hy4
      refine ⟨hr,z-w,by rw [map_sub,hz,hw],?_⟩
      rw [map_sub,hza,hwa,sub_self]
    exact boundaries_monotone H SphereSpectrum (11,136) (by decide : (3:ℤ)≤5)
      (weaky1_boundary_of_zero_representative (H:=H) (r:=4) (p:=(11,136)) hsub)


open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
private theorem weaky1_family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
private theorem weaky1_family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  rw [weaky1_family_map_data,weaky1_family_map_data,weaky1_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
private theorem weaky1_family_infinity_representative_map
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
  · rw [weaky1_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])
private theorem weaky1_sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (weaky1_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (weaky1_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (weaky1_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel

private theorem weaky1_finite_sphere_infinity_label_exists
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
    ∃ x : E2 H SphereSpectrum s t,
      HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D.quotientLabel q s t k x) e := by
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have heq : (D.family.functor.map f).eInftyMap (s,t,t-k)
      ((D.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
    change ((D.family.functor.map g).eInftyMap (s,t,t-k) ≫
      (D.family.functor.map f).eInftyMap (s,t,t-k)) e=e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  obtain ⟨c,hc⟩ := Quotient.exists_rep (P ((D.family.functor.map g).eInftyMap (s,t,t-k) e))
  have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hc.symm
  have hl : familyPageMap D.family f 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k c.val)=D.quotientLabel q s t k c.val := by
    rw [←weaky1_sphere_quotient_label_to_nu (D:=D) q k s t c.val]
    calc
      _ = familyPageMap D.family (g≫f) 2 (s,t,t-k) (D.quotientLabel q s t k c.val) :=
        ConcreteCategory.congr_hom (weaky1_family_page_comp (D:=D) g f 2 (s,t,t-k)) _
      _ = D.quotientLabel q s t k c.val := by
        rw [hgf,weaky1_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
          (s,t,t-k) ↑(2-2:ℤ).toNat) _
  have h := weaky1_family_infinity_representative_map f (s,t,t-k) _ _ hn
  rw [hl,heq] at h
  exact ⟨c.val,h⟩

private theorem weaky1_finite_sphere_filtration_has_label
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    ∃ x : E2 H SphereSpectrum s t,
      Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (XModLambdaN (S_0_0 : Syn) q)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (t-s,t-k)))
      (F.F s (t-s,t-k)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let gr := F.toAssociatedGraded s (t-s,t-k) a'
  let e := ((D.quotientConvergence q hq).identification (s,t,t-k)).inv gr
  have he : ((D.quotientConvergence q hq).identification (s,t,t-k)).hom e=gr :=
    ConcreteCategory.congr_hom ((D.quotientConvergence q hq).identification (s,t,t-k)).inv_hom_id gr
  obtain ⟨x,hx⟩ := weaky1_finite_sphere_infinity_label_exists BHS q k hq hkq s t e
  exact ⟨x,e,hx,a',ha',he⟩

private theorem weaky1_y_basis_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y=I.interpretation.basis .sphere 11 136 3 := by
  have hc := I.monomials (⟨.sphere,11,136,["69,1,89,1","1,1,389,1","1,1,388,1","0,2,391,1","0,3,375,1"]⟩ : Raw.Degree) (by
    unfold Raw.degrees
    iterate 192 apply List.mem_cons_of_mem
    exact List.mem_cons_self) rfl
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

private theorem weaky1_main_y_infty_label (I:AdamsComputationTheorems D L G) (BHS:EInftyComparison D)
    (e:((D.family.quotient (S_0_0:Syn) 9).sequence.ssData (11,136,132)).eInfty)
    (hne:e≠0) :
    HasInfinityRepresentative (D.family.quotient (S_0_0:Syn) 9) 2 (11,136,132)
      (D.quotientLabel 9 11 136 4 (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y)) e := by
  let P:=BHS.presentation.finiteWindow SphereSpectrum 9 (by decide) (11,136) 132 (by norm_num)
  let f:=XModLambdaN.map D.nu.unitIso.hom 9
  let g:=XModLambdaN.map D.nu.unitIso.inv 9
  have hgf:g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have heq:(D.family.functor.map f).eInftyMap (11,136,132)
      ((D.family.functor.map g).eInftyMap (11,136,132) e)=e := by
    change ((D.family.functor.map g).eInftyMap (11,136,132)≫
      (D.family.functor.map f).eInftyMap (11,136,132)) e=e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  obtain ⟨c,hc⟩:=Quotient.exists_rep (P ((D.family.functor.map g).eInftyMap (11,136,132) e))
  have hn:¬c.val∈boundaries H SphereSpectrum 5 (11,136) := by
    intro hb
    have hz:NestedQuotient.projection _ _ c=0:=(NestedQuotient.projection_eq_zero c).mpr hb
    have hzP:P ((D.family.functor.map g).eInftyMap (11,136,132) e)=0:=hc.symm.trans hz
    have hzE:(D.family.functor.map g).eInftyMap (11,136,132) e=0:=P.injective (hzP.trans (map_zero P).symm)
    apply hne
    rw [←heq,hzE,map_zero]
  have hb:= (weaky1_main_y_finite_cosets I c.val c.property).resolve_left hn
  let Y:Page D .sphere 11 136:=I.interpretation.basis .sphere 11 136 3
  have hY:Y∈cycles H SphereSpectrum 5 (11,136) := by
    have hh:=(cycles H SphereSpectrum 5 (11,136)).sub_mem c.property
      (boundaries_le_cycles H SphereSpectrum (11,136) 5 5 hb)
    simpa only [sub_sub_cancel] using hh
  let y:cycles H SphereSpectrum 5 (11,136):=⟨Y,hY⟩
  have hcy:NestedQuotient.projection (cycles H SphereSpectrum 5 (11,136)) (boundaries H SphereSpectrum 5 (11,136)) c=NestedQuotient.projection (cycles H SphereSpectrum 5 (11,136)) (boundaries H SphereSpectrum 5 (11,136)) y := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (NestedQuotient.projection_eq_zero ((show cycles H SphereSpectrum 5 (11,136) from c)-y)).mpr hb
  have hy:HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum 9) 2 (11,136,132)
      (finiteTargetLabel D .sphere 9 11 136 4 Y)
      ((D.family.functor.map g).eInftyMap (11,136,132) e) := by
    apply (BHS.labels.1 .sphere 9 (by decide) (11,136) 4 (by decide) y _).mpr
    exact hc.symm.trans hcy
  have hl:familyPageMap D.family f 2 (11,136,132)
      (finiteTargetLabel D .sphere 9 11 136 4 Y)=D.quotientLabel 9 11 136 4 Y := by
    rw [←weaky1_sphere_quotient_label_to_nu (D:=D) 9 4 11 136 Y]
    calc
      _=familyPageMap D.family (g≫f) 2 (11,136,132) (D.quotientLabel 9 11 136 4 Y) :=
        ConcreteCategory.congr_hom (weaky1_family_page_comp (D:=D) g f 2 (11,136,132)) _
      _=D.quotientLabel 9 11 136 4 Y := by
        rw [hgf,weaky1_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0:Syn) 9)).ssData (11,136,132) ↑(2-2:ℤ).toNat) _
  have hh:=weaky1_family_infinity_representative_map f (11,136,132) _ _ hy
  rw [hl,heq] at hh
  change HasInfinityRepresentative (D.family.quotient (S_0_0:Syn) 9) 2 (11,136,132)
    (D.quotientLabel 9 11 136 4 Y) e at hh
  dsimp only [Y] at hh
  erw [←weaky1_y_basis_label I] at hh
  exact hh

private theorem weaky1_main_y_detected_of_filtration_bounds (I:AdamsComputationTheorems D L G) (BHS:EInftyComparison D)
    (z:BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (h11:FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 z)
    (h12:¬FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 z) :
    FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) z := by
  obtain ⟨x,hx⟩:=weaky1_finite_sphere_filtration_has_label BHS 9 4 (by decide) (by decide) 11 136 z h11
  obtain ⟨e,he,a,ha,hgr⟩:=hx
  have hn:e≠0 := by
    intro hz
    apply h12
    exact detects_zero_infinity_filtration (D.quotientConvergence 9 (by decide)) (11,136,132)
      ⟨e,he,a,ha,hgr⟩ (hz ▸ he)
  have hy:=weaky1_main_y_infty_label I BHS e hn
  exact ⟨⟨e,hy,a,ha,hgr⟩,⟨e,hy,hn⟩⟩

end KIP126.Computation.SphereAndCofiber

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2 KIP126.Algebra PageRepresentatives
open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
private theorem weaky_sphere_quotient_high_filtration_zero (BHS : EInftyComparison D)
    (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
    (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
    (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) N z) : z=0 := by
  let O : SyntheticObject := .quotient q .sphere
  have hsep : ∀ z : BiHom m w (O.obj D.nu D.hopfAndDetector),
      (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) j z) → z=0 :=
    D.homotopySeparated O m w
  refine (D.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
  intro j hj
  let i : Tridegree := (j,m+j,w)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
  have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
  haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
    dsimp only [PageRepresentatives.finiteEInftyModel]
    rw [if_neg hh]
    infer_instance
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (D.family.functor.map g).eInftyMap i e=0 :=
    P.injective (Subsingleton.elim _ _)
  have h := congrArg (fun a=>(D.family.functor.map f).eInftyMap i a) he
  change ((D.family.functor.map g).eInftyMap i ≫ (D.family.functor.map f).eInftyMap i) e=_ at h
  rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
    CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
  simpa only [ConcreteCategory.id_apply,map_zero] using h

private theorem weaky_lambda_filtration_preserved {A : Syn} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = _
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = a at hz
  dsimp only [lambdaMultiply]
  simp only [Category.assoc,hz]


private theorem y_detected_of_filtration_eleven_and_nonzero
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D)
    (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hd : Detects D.sphereConvergence (1,1,1)
      (D.sphereE2 1 1 0 (Sphere.Internal.hi H M 0)) h0)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hf11 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 y0)
    (hne : lambdaMultiply 2 (sphereAction h0 y0)≠0) :
    FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y0 := by
  apply weaky1_main_y_detected_of_filtration_bounds I BHS y0 hf11
  intro hf12
  have hf14 := (weaky0_weight132_filtration_twelve_fourteen I BHS y0).mp hf12
  have hf15 := weaky0_h0_increases_fourteen BHS A ab h0 hd y0 hf14
  have hf := weaky_lambda_filtration_preserved 2 15 (sphereAction h0 y0) hf15
  exact hne (weaky_sphere_quotient_high_filtration_zero BHS 9 (by decide)
    125 131 15 (by decide) (lambdaMultiply 2 (sphereAction h0 y0)) hf)

private theorem y_detected_of_filtration_bounds
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D)
    (A : AdamsAlgebraStructures D) (ab : AlgebraDetectionCompatibility D A)
    (eta : BiHom 1 2 (S_0_0 : Syn)) (low : TodaRelations D eta)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hf11 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 y0)
    (hne : lambdaMultiply 2 (sphereAction low.h0 y0)≠0) :
    FiniteDetected D 9 (by decide) 11 136 4
      (I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y) y0 := by
  exact y_detected_of_filtration_eleven_and_nonzero I BHS A ab low.h0
    (weaky0_h0_source_detected eta low) y0 hf11 hne

end KIP126.Computation.SphereAndCofiber
