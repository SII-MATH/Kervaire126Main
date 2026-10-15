module

public import Batteries.Tactic.OpenPrivate
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import Init.Data.String.Lemmas.Splits
public import KIP126.Def.SpectralSequence.Basic.Data
public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.SpectralSequence.Basic.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Data
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
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
public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Consequences
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Stem125Differentials
public import KIP126.Main.SectionSeven.CofiberFiltration
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.Model.Classes.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.Predicates

@[expose] public section

namespace KIP126.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}

private theorem y_detection_page_represents_unique {a b : E.Page r p}
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

private theorem y_detection_page_represents_d_zero_of_later {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
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
  rw [y_detection_page_represents_unique ha hrep]
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
private theorem y_detection_page_next_projection_zero_iff_incoming
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
universe u v
variable {R : Type u} [Ring R]
private theorem y_detection_page_represents_before
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
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}

private theorem y_detection_page_differential_target_later_zero
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

private theorem y_detection_page_represents_add_tail
    {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
    RepresentsOnPage E r p (x+y) (a+b) := by
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩

open PageRepresentatives

private theorem y_detection_page_af16_source_frame (I : AdamsComputationTheorems D L G)
    (x : (sequence D .sphere).Page 2 (16,141))
    (hc : x ∈ cycles H SphereSpectrum 7 (16,141)) :
    x=0 ∨ x=I.interpretation.basis .sphere 16 141 1 ∨ x=I.interpretation.basis .sphere 16 141 2 ∨ x=I.interpretation.basis .sphere 16 141 1+I.interpretation.basis .sphere 16 141 2 := by
  let E := sequence D .sphere
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (I.interpretation.basis .sphere 14 140 1) (I.interpretation.basis .sphere 16 141 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      unfold Raw.claims
      iterate 369 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      unfold Raw.claims
      iterate 370 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 0) (I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
      unfold Raw.claims
      iterate 371 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [0, 1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 3) (I.interpretation.basis .sphere 18 142 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
      unfold Raw.claims
      iterate 372 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 232 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 245 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 18 142 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h370
  have hd' : E.d 4 (12,138) u=v := hd
  have hdv : E.d 4 (16,141) v=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(12,138)) ⟨u,hd'⟩
  have hv2 : RepresentsOnPage E 2 (16,141) (I.interpretation.basis .sphere 16 141 1)
      (I.interpretation.basis .sphere 16 141 1) := by
    obtain ⟨b,hb⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd1 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 1)=0 :=
    y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hv2 ⟨v,hv⟩
  have hz2 : RepresentsOnPage E 4 (16,141) (I.interpretation.basis .sphere 16 141 2) 0 :=
    y_detection_page_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hd2 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 2)=0 := by
    obtain ⟨b,hb⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz2
    rw [←hb.eq_on_page_two] at hb
    exact y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz2⟩
  have hd0 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 0) =
      I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 3) =
      I.interpretation.basis .sphere 18 142 1 := h372.eq_on_page_two.2
  obtain ⟨xc,hxc⟩ := (isCycle_iff_represents H SphereSpectrum 8 (by decide) (16,141) x).mp ⟨by decide,hc⟩
  change RepresentsOnPage E 8 (16,141) x xc at hxc
  have hx : E.d 2 (16,141) x=0 := by
    obtain ⟨x2,hx2⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤8) hxc
    have h := y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<8) hx2 ⟨xc,hxc⟩
    simpa only [hx2.eq_on_page_two] using h
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    exact Or.inl hxe
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he2] at hxe
    exact Or.inr (Or.inr (Or.inl hxe))
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he1] at hxe
    exact Or.inr (Or.inl hxe)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    simp only [he1, he2] at hxe
    exact Or.inr (Or.inr (Or.inr hxe))
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem y_detection_page_af15_source_frame (I : AdamsComputationTheorems D L G)
    (x : (sequence D .sphere).Page 2 (15,140))
    (hc : x ∈ cycles H SphereSpectrum 8 (15,140)) :
    x=0 ∨ x=I.interpretation.basis .sphere 15 140 1 ∨ x=I.interpretation.basis .sphere 15 140 4 ∨ x=I.interpretation.basis .sphere 15 140 1+I.interpretation.basis .sphere 15 140 4 := by
  let E := sequence D .sphere
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (I.interpretation.basis .sphere 13 139 1) (I.interpretation.basis .sphere 15 140 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      unfold Raw.claims
      iterate 354 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      unfold Raw.claims
      iterate 355 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h357 : HasDifferential E 2 (15,140) (17,141)
      (I.interpretation.basis .sphere 15 140 0) (I.interpretation.basis .sphere 17 141 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,140,[0],17,141,[3],"S0_AdamsE2_ss",3153⟩ (by
      unfold Raw.claims
      iterate 357 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 17 141 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h358 : HasDifferential E 2 (15,140) (17,141)
      (I.interpretation.basis .sphere 15 140 3) (I.interpretation.basis .sphere 17 141 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,140,[3],17,141,[1],"S0_AdamsE2_ss",3154⟩ (by
      unfold Raw.claims
      iterate 358 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 17 141 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,140,["456,1", "67,1,107,1", "1,1,439,1", "0,1,449,1", "0,3,425,1"]⟩ (by
    unfold Raw.degrees
    iterate 224 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 140 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 15 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 15 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 15 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 15 140 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 15 140 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,141,["472,1", "0,2,448,1", "0,3,440,1", "0,3,439,1"]⟩ (by
    unfold Raw.degrees
    iterate 239 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 141 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 17 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 17 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 17 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 17 141 3 := hf 3
  obtain ⟨xraw,yraw,hx,hy,hd⟩ := stem125_af15_nonzero_d5 I
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  obtain ⟨_,u,v,hu,hv,hd,hn⟩ := hd
  have hd' : E.d 5 (15,140) u=v := hd
  have hz1 : RepresentsOnPage E 5 (15,140) (I.interpretation.basis .sphere 15 140 1) 0 :=
    y_detection_page_differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h355
  have hz4 : RepresentsOnPage E 5 (15,140) (I.interpretation.basis .sphere 15 140 4) 0 :=
    y_detection_page_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h354
  have hd1 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 1)=0 := by
    obtain ⟨b,hb⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    rw [←hb.eq_on_page_two] at hb
    exact y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz1⟩
  have hd2 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 2)=0 := by
    obtain ⟨b,hb⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hu
    rw [←hb.eq_on_page_two] at hb
    exact y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨u,hu⟩
  have hd4 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 4)=0 := by
    obtain ⟨b,hb⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz4
    rw [←hb.eq_on_page_two] at hb
    exact y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz4⟩
  have hd0 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 0)=I.interpretation.basis .sphere 17 141 3 := h357.eq_on_page_two.2
  have hd3 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 3)=I.interpretation.basis .sphere 17 141 1 := h358.eq_on_page_two.2
  obtain ⟨xc,hxc⟩ := (isCycle_iff_represents H SphereSpectrum 9 (by decide) (15,140) x).mp ⟨by decide,hc⟩
  change RepresentsOnPage E 9 (15,140) x xc at hxc
  have hx : E.d 2 (15,140) x=0 := by
    obtain ⟨x2,hx2⟩ := y_detection_page_represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤9) hxc
    have h := y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<9) hx2 ⟨xc,hxc⟩
    simpa only [hx2.eq_on_page_two] using h
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  generalize hc4 : e x 4=c4 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    exact Or.inl hxe
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he4] at hxe
    exact Or.inr (Or.inr (Or.inl hxe))
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he3, he4, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he2]
      simpa only [zero_add,add_zero] using hu
    exact hd'.symm.trans (y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he2, he4]
      simpa only [zero_add,add_zero] using y_detection_page_represents_add_tail (hu) hz4
    exact hd'.symm.trans (y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, he4, hd2, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he1] at hxe
    exact Or.inr (Or.inl hxe)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    simp only [he1, he4] at hxe
    exact Or.inr (Or.inr (Or.inr hxe))
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, he4, hd1, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he1, he2]
      simpa only [zero_add,add_zero] using y_detection_page_represents_add_tail (hz1) hu
    exact hd'.symm.trans (y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he1, he2, he4]
      simpa only [zero_add,add_zero] using y_detection_page_represents_add_tail (y_detection_page_represents_add_tail (hz1) hu) hz4
    exact hd'.symm.trans (y_detection_page_represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, he4, hd1, hd2, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he4, hd0, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, he4, hd0, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he4, hd0, hd2, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, he4, hd0, hd2, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he4, hd0, hd1, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, he4, hd0, hd1, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he4, hd0, hd1, hd2, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, he4, hd0, hd1, hd2, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

open KIP126.Synthetic.SpectralSequence KIP126.Literature.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven KIP126.Algebra
private theorem y_detection_page_represents_zero_iff_boundary (X : C) (r : ℤ) (hr : 2≤r)
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

private theorem y_detection_page_boundary_hit_or_previous (X : C) (r : ℤ) (hr : 2≤r)
    (p : ℤ×ℤ) (x : PageRepresentatives.Ambient H X p)
    (hx : x∈PageRepresentatives.boundaries H X r p) :
    x∈PageRepresentatives.boundaries H X (r-1) p ∨
      HitOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x := by
  let E := adamsTowerInternalSpectralSequence H.unit X
  obtain ⟨q,rfl⟩ : ∃ q : ℤ×ℤ, q+E.diffDeg r=p := ⟨p-E.diffDeg r,sub_add_cancel _ _⟩
  let A := E.ssData (q+E.diffDeg r)
  let n := (r-2).toNat
  have hn : (r-1).toNat=n+1 := by dsimp [n]; omega
  change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1).toNat (q+E.diffDeg r)).hom b=x at hx
  rw [hn] at hx
  obtain ⟨b,hb⟩ := hx
  let z := (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _)) b
  have hz : A.pageπ ↑(n+1) z=0 := by
    change (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _) ≫
      cokernel.π (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _))) b=0
    rw [cokernel.condition]
    rfl
  have hnm : (↑n:WithTop ℕ)≤↑(n+1) := by exact_mod_cast Nat.le_succ n
  let y := (Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm) ≫ A.pageπ ↑n) z
  have hym : y∈LinearMap.range (E.d r q).hom :=
    (y_detection_page_next_projection_zero_iff_incoming E r (by change (2:ℤ)≤r; exact hr) q z).mp hz
  have hy : RepresentsOnPage E r (q+E.diffDeg r) x y := by
    refine ⟨hr,(Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm)) z,?_,rfl⟩
    change (Subobject.ofLE (A.Z ↑n) (A.Z 0) _ ≫ A.pageπ 0)
      ((Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm)) z)=x
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    change (Subobject.ofLE (A.Z ↑(n+1)) (A.Z 0) _ ≫ A.pageπ 0)
      ((Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _)) b)=x
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hb
  by_cases hy0 : y=0
  · left
    rw [hy0] at hy
    exact (y_detection_page_represents_zero_iff_boundary X r hr (q+E.diffDeg r) x).mp hy
  · right
    obtain ⟨a,ha⟩ := hym
    exact ⟨q,rfl,a,y,hy,hy0,by simpa using ha⟩

private theorem y_detection_page_sphere_first_label_transport (s t : ℤ)
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

private theorem y_detection_page_sphere_boundary_torsion_lift
    (R : RealizationDetectionData D) (s t : ℤ) (r : ℕ) (hr : 2≤r)
    (x : E2 H SphereSpectrum s t)
    (hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t))
    (hx : HitOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn),
      D.sphereFirstQuotient s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
  obtain ⟨a,ha,hat⟩ := R.detection.boundary_lift .sphere s t r hr x hp hx
  let e := SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  refine ⟨a≫e,?_,?_⟩
  · have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
      unfold quotientClass
      simp only [Category.assoc]
      exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
    rw [hc,ha]
    exact y_detection_page_sphere_first_label_transport s t x
  · simpa only [lambdaMultiply,Category.assoc,Limits.zero_comp] using
      congrArg (fun f=>f≫e) hat

private theorem y_detection_page_lambda_multiply_zero_mono (D : AdamsComparison H M Syn) {A : Syn} (a b : ℕ) (hab : a≤b)
    {m w : ℤ} (x : BiHom m w A) (hx : lambdaMultiply a x=0) :
    lambdaMultiply b x=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at hx ⊢
  rw [lambdaPow_add D.shiftCoherence (b-a) a b (Nat.sub_add_cancel hab)]
  simp only [Category.assoc,hx,Limits.comp_zero]

private theorem y_detection_page_sphere_boundary_submodule_torsion_lift
    (R : RealizationDetectionData D) (s t : ℤ) (r : ℕ) (hr : 1≤r)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.boundaries H SphereSpectrum r (s,t)) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn),
      D.sphereFirstQuotient s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr1 : r=1
    · subst r
      have hx0 : x=0 := by simpa only [Nat.cast_one,PageRepresentatives.boundaries_one,Submodule.mem_bot] using hx
      subst x
      refine ⟨0,?_,?_⟩ <;> simp only [quotientClass,lambdaMultiply,Limits.zero_comp,Limits.comp_zero,map_zero]
    · have hr2 : 2≤r := by omega
      rcases y_detection_page_boundary_hit_or_previous SphereSpectrum r (by omega) (s,t) x hx with hp|hh
      · have hprev : x∈PageRepresentatives.boundaries H SphereSpectrum ((r-1:ℕ):ℤ) (s,t) := by
          simpa only [Nat.cast_sub hr,Nat.cast_one] using hp
        obtain ⟨a,ha,hat⟩ := ih (r-1) (by omega) (by omega) hprev
        exact ⟨a,ha,y_detection_page_lambda_multiply_zero_mono (D:=D) (r-1-1) (r-1) (by omega) a hat⟩
      · exact y_detection_page_sphere_boundary_torsion_lift R s t r hr2 x
          (PageRepresentatives.boundaries_le_permanentCycles H SphereSpectrum (s,t) r hx) hh

private theorem y_detection_page_family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
private theorem y_detection_page_family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  rw [y_detection_page_family_map_data,y_detection_page_family_map_data,y_detection_page_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
private theorem y_detection_page_family_infinity_representative_map
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
  · rw [y_detection_page_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])
private theorem y_detection_page_sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (y_detection_page_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (y_detection_page_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (y_detection_page_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel

private theorem y_detection_page_finite_sphere_infinity_cycle_label_exists
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
    ∃ x : E2 H SphereSpectrum s t,
      x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
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
    rw [←y_detection_page_sphere_quotient_label_to_nu (D:=D) q k s t c.val]
    calc
      _ = familyPageMap D.family (g≫f) 2 (s,t,t-k) (D.quotientLabel q s t k c.val) :=
        ConcreteCategory.congr_hom (y_detection_page_family_page_comp (D:=D) g f 2 (s,t,t-k)) _
      _ = D.quotientLabel q s t k c.val := by
        rw [hgf,y_detection_page_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
          (s,t,t-k) ↑(2-2:ℤ).toNat) _
  have h := y_detection_page_family_infinity_representative_map f (s,t,t-k) _ _ hn
  rw [hl,heq] at h
  refine ⟨c.val,?_,h⟩
  convert c.property using 1; congr 1; omega

private theorem y_detection_page_finite_sphere_filtration_has_cycle_label
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    ∃ x : E2 H SphereSpectrum s t,
      x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
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
  obtain ⟨x,hc,hx⟩ := y_detection_page_finite_sphere_infinity_cycle_label_exists BHS q k hq hkq s t e
  exact ⟨x,hc,e,hx,a',ha',he⟩

private theorem y_detection_page_detected_map
    (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
    (i : Tridegree) (x : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (ha : Detects (D.convergence X) i x a) :
    Detects (D.convergence Y) i (familyPageMap D.family f 2 i x) (a≫f) := by
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
  refine ⟨(D.family.functor.map f).eInftyMap i e,y_detection_page_family_infinity_representative_map f i x e he,k a',?_,?_⟩
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

private theorem y_detection_page_sphere_quotient_high_filtration_zero (BHS : EInftyComparison D)
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

private theorem y_detection_page_boundary_of_zero_representative
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

private theorem y_detection_page_af15_source_boundary (I : AdamsComputationTheorems D L G) :
    cycles H SphereSpectrum 8 (15,140) ≤ boundaries H SphereSpectrum 4 (15,140) := by
  intro x hx
  let E := sequence D .sphere
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      unfold Raw.claims
      iterate 355 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (I.interpretation.basis .sphere 13 139 1) (I.interpretation.basis .sphere 15 140 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      unfold Raw.claims
      iterate 354 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have hb1 : I.interpretation.basis .sphere 15 140 1 ∈ boundaries H SphereSpectrum 4 (15,140) :=
    y_detection_page_boundary_of_zero_representative (r:=5) (p:=(15,140))
      (y_detection_page_differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h355)
  have hb4 : I.interpretation.basis .sphere 15 140 4 ∈ boundaries H SphereSpectrum 4 (15,140) :=
    y_detection_page_boundary_of_zero_representative (r:=5) (p:=(15,140))
      (y_detection_page_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h354)
  rcases y_detection_page_af15_source_frame I x hx with rfl|rfl|rfl|rfl
  · exact Submodule.zero_mem _
  · exact hb1
  · exact hb4
  · exact Submodule.add_mem _ hb1 hb4
private theorem y_detection_page_af16_source_boundary (I : AdamsComputationTheorems D L G) :
    cycles H SphereSpectrum 7 (16,141) ≤ boundaries H SphereSpectrum 4 (16,141) := by
  intro x hx
  let E := sequence D .sphere
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      unfold Raw.claims
      iterate 370 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (I.interpretation.basis .sphere 14 140 1) (I.interpretation.basis .sphere 16 141 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      unfold Raw.claims
      iterate 369 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have hb1 : I.interpretation.basis .sphere 16 141 1 ∈ boundaries H SphereSpectrum 4 (16,141) :=
    y_detection_page_boundary_of_zero_representative (r:=5) (p:=(16,141))
      (y_detection_page_differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h370)
  have hb2 : I.interpretation.basis .sphere 16 141 2 ∈ boundaries H SphereSpectrum 4 (16,141) :=
    y_detection_page_boundary_of_zero_representative (r:=5) (p:=(16,141))
      (y_detection_page_differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h369)
  rcases y_detection_page_af16_source_frame I x hx with rfl|rfl|rfl|rfl
  · exact Submodule.zero_mem _
  · exact hb1
  · exact hb2
  · exact Submodule.add_mem _ hb1 hb2
omit [HasFunctorialCofiber (C := Syn)] in
private theorem y_detection_page_lambda_multiply_zero_precomp {A : Syn} {m w m' w' : ℤ}
    (b : ℕ) (f : Smn (Syn:=Syn) m' w' ⟶ Smn m w) (x : BiHom m w A)
    (hx : lambdaMultiply b x=0) : lambdaMultiply b (f≫x)=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at hx ⊢
  rw [←Category.assoc,←lambdaPow_naturality b f,Category.assoc,hx,Limits.comp_zero]

omit [HasFunctorialCofiber (C := Syn)] in
private theorem y_detection_page_lambda_multiply_zero_iterated {A : Syn} {m w : ℤ}
    (a b : ℕ) (x : BiHom m w A) (hx : lambdaMultiply b x=0) :
    lambdaMultiply b (lambdaMultiply a x)=0 := by
  let f : Smn (Syn:=Syn) m (w-a) ⟶ Smn m w :=
    eqToHom (by congr 1; simp) ≫
      (SyntheticCategory.biShift_comp (m,w) (0,-(a:ℤ))).inv.app S_0_0 ≫ lambdaPow a (Smn m w)
  have he : lambdaMultiply a x=f≫x := by simp only [f,lambdaMultiply,Category.assoc]
  rw [he]
  exact y_detection_page_lambda_multiply_zero_precomp b f x hx

private theorem y_detection_page_boundary_filtration_peel
    (BHS : EInftyComparison D) (R : RealizationDetectionData D)
    (s t : ℤ) (k : ℕ) (hk : k<9)
    (hb : cycles H SphereSpectrum (9-k) (s,t) ≤ boundaries H SphereSpectrum 4 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) 9))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    ∃ a' : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (s+1) a' ∧
      lambdaMultiply 6 a'=lambdaMultiply 6 a := by
  obtain ⟨x,hxc,hxa⟩ := y_detection_page_finite_sphere_filtration_has_cycle_label BHS 9 k (by decide) hk s t a ha
  obtain ⟨b,hbq,hbt⟩ := y_detection_page_sphere_boundary_submodule_torsion_lift R s t 4 (by decide) x (hb hxc)
  let a0 : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) 9) := quotientClass 9 (lambdaMultiply k b)
  have ha0 : Detects (D.quotientConvergence 9 (by decide)) (s,t,t-k) (D.quotientLabel 9 s t k x) a0 := by
    have h := D.comparisonCompatible.homotopy_lambda s t k b
    rw [hbq] at h
    exact y_detection_page_detected_map .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9) (s,t,t-k) _ _ h
  have ha0zero : lambdaMultiply 6 a0=0 := by
    have hb6 := y_detection_page_lambda_multiply_zero_mono D 3 6 (by decide) b hbt
    have hb6k := y_detection_page_lambda_multiply_zero_iterated k 6 b hb6
    simpa only [a0,quotientClass,lambdaMultiply,Category.assoc,Limits.zero_comp] using
      congrArg (fun f=>f≫XModLambdaN.incl (S_0_0 : Syn) 9) hb6k
  refine ⟨a-a0,detects_sub_filtration (D.quotientConvergence 9 (by decide)) (s,t,t-k) hxa ha0,?_⟩
  have hdist : lambdaMultiply 6 (a-a0)=lambdaMultiply 6 a-lambdaMultiply 6 a0 := by
    simp only [lambdaMultiply,Preadditive.comp_sub]
  rw [hdist,ha0zero,sub_zero]

private theorem y_detection_page_lambda_filtration_preserved {A : Syn} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = _
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = a at hz
  dsimp only [lambdaMultiply]
  simp only [Category.assoc,hz]

private theorem y_detection_page_lambda_six_filtration_fifteen_zero
    (I : AdamsComputationTheorems D L G) (BHS : EInftyComparison D) (R : RealizationDetectionData D)
    (a : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) :
    lambdaMultiply 6 a=0 := by
  obtain ⟨b,hb,hab⟩ := y_detection_page_boundary_filtration_peel BHS R 15 140 1 (by decide)
    (y_detection_page_af15_source_boundary I) a ha
  obtain ⟨c,hc,hbc⟩ := y_detection_page_boundary_filtration_peel BHS R 16 141 2 (by decide)
    (y_detection_page_af16_source_boundary I) b hb
  have hc17 := y_detection_page_lambda_filtration_preserved 6 17 c hc
  have hz := y_detection_page_sphere_quotient_high_filtration_zero BHS 9 (by decide) 125 133 17 (by decide)
    (lambdaMultiply 6 c) hc17
  exact hab.symm.trans (hbc.symm.trans hz)

end KIP126.Computation.SphereAndCofiber

namespace KIP126.StableHomotopy.Toda
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [IsTriangulated C]
set_option backward.isDefEq.respectTransparency false

private theorem y_detection_toda_juggling_every_member
    {X Y Z W V:C} {f:X⟶Y} {g:Y⟶Z} {h:Z⟶W} {d:W⟶V}
    {x:X⟦(1:ℤ)⟧⟶W} (hx:Relation x f g h)
    (hhd:h≫d=0)
    (hind:∀u:Y⟦(1:ℤ)⟧⟶W,f⟦(1:ℤ)⟧'≫u=0)
    {y:Y⟦(1:ℤ)⟧⟶V} (hy:Relation y g h d) :
    x≫d=(-f⟦(1:ℤ)⟧')≫y := by
  obtain ⟨x',hx',he⟩ := (shuffle_iff f g h d (composable hx).1
    (composable hx).2 hhd ((-f⟦(1:ℤ)⟧')≫y)).mpr ⟨y,hy,rfl⟩
  obtain ⟨u,v,huv⟩:=indeterminacy_complete hx hx'
  have hh:=congrArg (fun a => a≫d) huv
  simp only [Preadditive.sub_comp,Preadditive.add_comp,Category.assoc,hhd,
    comp_zero,hind u,zero_comp,add_zero] at hh
  exact (sub_eq_zero.mp hh).trans he

end KIP126.StableHomotopy.Toda

namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Literature.AdamsSynthetic
open KIP126.AdamsSynthetic.SectionSeven
universe u v
variable {Syn:Type u} [SyntheticCategory.{u,v} Syn]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem y_detection_toda_shifted_h0_low_indeterminacy
    (h0:BiHom 0 1 (S_0_0:Syn))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    (u:((SyntheticCategory.biShift (1,3)).obj (S_0_0:Syn))⟦(1:ℤ)⟧⟶(S_0_0:Syn)) :
    ((SyntheticCategory.biShift (1,3)).map h0)⟦(1:ℤ)⟧'≫u=0 := by
  let G:=SyntheticCategory.biShift (Syn:=Syn) (1,3)
  let K:=SyntheticCategory.biShift (Syn:=Syn) (2,3)
  let j:G⋙shiftFunctor Syn (1:ℤ)≅K :=
    Functor.isoWhiskerLeft G (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm ≪≫
      SyntheticCategory.biShift_comp (1,3) (1,0)
  let a:BiHom 2 3 (S_0_0:Syn):=j.inv.app (S_0_0:Syn)≫u
  have hz:K.map h0≫a=0 := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (0,1) (2,3)).inv.app (S_0_0:Syn))).mp
    simpa only [sphereProduct,comp_zero] using hind a
  have hn:=j.hom.naturality h0
  have hh:=congrArg (fun k => k≫a) hn
  dsimp only [Functor.comp_map] at hh
  have hu:j.hom.app (S_0_0:Syn)≫a=u := by
    dsimp only [a]
    simp only [j.hom_inv_id_app_assoc]
  rw [Category.assoc,hu,Category.assoc,hz,comp_zero] at hh
  exact hh

private theorem y_detection_toda_map_left_indeterminacy
    (F:Syn⥤Syn) [F.CommShift ℤ] [F.Additive] (ff:F.FullyFaithful)
    {A B W:Syn} (f:A⟶B)
    (hind:∀u:B⟦(1:ℤ)⟧⟶W,f⟦(1:ℤ)⟧'≫u=0)
    (u:(F.obj B)⟦(1:ℤ)⟧⟶F.obj W) :
    (F.map f)⟦(1:ℤ)⟧'≫u=0 := by
  let j:=F.commShiftIso (1:ℤ)
  let u0:B⟦(1:ℤ)⟧⟶W:=ff.preimage (j.hom.app B≫u)
  have hu:F.map u0=j.hom.app B≫u:=ff.map_preimage _
  have hh:=congrArg F.map (hind u0)
  simp only [Functor.map_comp,Functor.map_zero] at hh
  rw [hu] at hh
  have hn:=j.inv.naturality f
  have hnu:=congrArg (fun a => a≫j.hom.app B≫u) hn
  simp only [Functor.comp_map,Category.assoc,j.inv_hom_id_app_assoc] at hnu
  rw [hh,comp_zero] at hnu
  exact hnu

private theorem y_detection_toda_module_low_shuffle_raw
    [IsTriangulated Syn]
    [(SyntheticCategory.biShift (Syn:=Syn) (123,129)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (123,129)).IsTriangulated]
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    {X:Syn} (a:BiHom 123 129 X) (ha:sphereAction h0 a=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda a h0 eta z) :
    let F:=SyntheticCategory.biShift (Syn:=Syn) (123,129)
    let d:F.obj (Smn (Syn:=Syn) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:Syn)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    ((F.commShiftIso (1:ℤ)).inv.app ((SyntheticCategory.biShift (1,3)).obj (Smn 0 1)) ≫
      F.map ((tripleTodaSource (Syn:=Syn) 0 1 1 2 0 1).inv ≫ sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))≫a =
      (-(F.map ((SyntheticCategory.biShift (1,3)).map h0))⟦(1:ℤ)⟧')≫
        d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=Syn) 1 2 0 1 123 129).inv≫z := by
  dsimp only
  let F:=SyntheticCategory.biShift (Syn:=Syn) (123,129)
  let d:F.obj (Smn (Syn:=Syn) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
    F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:Syn)).symm ≪≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
  let e: F.obj (Smn (Syn:=Syn) 0 1)≅Smn 123 130 :=
    (SyntheticCategory.biShift_comp (0,1) (123,129)).app (S_0_0:Syn)
  have hh:F.map h0≫a=0 := by
    apply (cancel_epi e.inv).mp
    simpa only [e,F,sphereAction,Category.assoc,comp_zero,Iso.app_inv,Int.reduceAdd] using ha
  have hmap:=Toda.map F hlow
  have hnorm:=Toda.precompose hz d.hom
  have hn:d.hom≫(SyntheticCategory.biShift (123,130)).map eta=
      F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:Syn)≫
        (SyntheticCategory.biShift (0,1)).map eta)≫e.hom := by
    change (F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:Syn)) ≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).hom.app (Smn 1 2)) ≫ _ = _
    simpa only [e,F,Functor.map_comp,Functor.comp_map,Category.assoc,Prod.mk_add_mk,Int.reduceAdd,
      Iso.app_hom] using
      congrArg (fun k => F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:Syn))≫k)
        ((SyntheticCategory.biShift_comp (0,1) (123,129)).hom.naturality eta).symm
  change Toda.Relation _ (d.hom≫(SyntheticCategory.biShift (123,130)).map eta)
    (e.inv≫F.map h0) a at hnorm
  rw [hn] at hnorm
  have hn':=Toda.absorb_first hnorm
  simp only [e.hom_inv_id_assoc] at hn'
  have hi:∀u:(F.obj ((SyntheticCategory.biShift (1,3)).obj (S_0_0:Syn)))⟦(1:ℤ)⟧⟶F.obj (S_0_0:Syn),
      (F.map ((SyntheticCategory.biShift (1,3)).map h0))⟦(1:ℤ)⟧'≫u=0 := by
    intro u
    exact y_detection_toda_map_left_indeterminacy F (SyntheticCategory.biShift_fullyFaithful (123,129))
      _ (y_detection_toda_shifted_h0_low_indeterminacy h0 hind) u
  have hresult:=Toda.y_detection_toda_juggling_every_member hmap hh hi hn'
  simpa only [F,d,Category.assoc,homotopyRegrade,Int.reduceAdd,eqToHom_refl,Category.id_comp] using hresult

private theorem y_detection_toda_module_low_source_iso (coh:BiShiftCoherence Syn) :
    let F:=SyntheticCategory.biShift (Syn:=Syn) (123,129)
    let d:F.obj (Smn (Syn:=Syn) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:Syn)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    d.hom=(SyntheticCategory.biShift_comp (1,3) (123,129)).hom.app (S_0_0:Syn)≫
      (SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:Syn) := by
  dsimp only
  have hh:=coh.associativity (1,2) (0,1) (123,129) (1,3) (123,130) (124,132)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:Syn)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hh
  have he:=congrArg (fun k =>
    (SyntheticCategory.biShift (123,129)).map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:Syn))≫
      k≫(SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:Syn)) hh
  simp only [←Category.assoc,←Functor.map_comp,Iso.inv_hom_id_app] at he
  simp only [Category.assoc,Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Smn,Functor.comp_obj,Prod.mk_add_mk,Int.reduceAdd,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,
    Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Iso.app_inv,Iso.app_hom] using he.symm

private theorem y_detection_toda_module_low_normalized_source (coh:BiShiftCoherence Syn) :
    let F:=SyntheticCategory.biShift (Syn:=Syn) (123,129)
    let G:=SyntheticCategory.biShift (Syn:=Syn) (1,3)
    let d:F.obj (Smn (Syn:=Syn) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:Syn)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    let J: (G⋙F)⋙shiftFunctor Syn (1:ℤ)≅SyntheticCategory.biShift (125,132):=
      Functor.isoWhiskerLeft (G⋙F) (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm ≪≫
        Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,3) (123,129))
          (SyntheticCategory.biShift (1,0)) ≪≫
            SyntheticCategory.biShift_comp (124,132) (1,0)
    d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=Syn) 1 2 0 1 123 129).inv=J.hom.app (S_0_0:Syn) := by
  dsimp only
  rw [y_detection_toda_module_low_source_iso coh]
  simp only [Functor.map_comp,Category.assoc]
  have hsrc : tripleTodaSource (Syn:=Syn) 1 2 0 1 123 129 =
      ((SyntheticCategory.biShift_comp (124,132) (1,0)).app (S_0_0:Syn)).symm ≪≫
        (SyntheticCategory.biShift (1,0)).mapIso
          ((SyntheticCategory.biShift_comp (1,2) (123,130)).app (S_0_0:Syn)).symm ≪≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).app
          ((SyntheticCategory.biShift (123,130)).obj (Smn 1 2)) := by rfl
  rw [hsrc]
  simp only [Iso.trans_inv,Iso.symm_inv,Functor.mapIso_inv,Iso.app_inv,Iso.app_hom,
    Iso.symm_hom,Iso.trans_hom,NatTrans.comp_app,Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,Functor.whiskerLeft_app,Functor.whiskerRight_app,Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_compat (Syn:=Syn) 1).inv.naturality
    ((SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:Syn)))]
  erw [((SyntheticCategory.biShift_comp (1,2) (123,130)).app (S_0_0:Syn)).map_inv_hom_id_assoc
    (SyntheticCategory.biShift (1,0))]
  erw [reassoc_of% ((SyntheticCategory.biShift_compat (Syn:=Syn) 1).inv.naturality
    ((SyntheticCategory.biShift_comp (1,3) (123,129)).hom.app (S_0_0:Syn)))]

private theorem y_detection_toda_source_iso_fixed_transport
    {A B U X:Syn} (F:Syn⥤Syn) (ff:F.FullyFaithful)
    (f:A⟶B) (hf:∀a:A≅A,a.hom≫f=f) (d:U≅F.obj A) (x:F.obj B⟶X)
    (a:U≅U) : a.hom≫d.hom≫F.map f≫x=d.hom≫F.map f≫x := by
  let b:=ff.preimageIso (d.symm≪≫a≪≫d)
  have hb:F.map b.hom=d.inv≫a.hom≫d.hom := ff.map_preimage _
  have hh:=congrArg F.map (hf b)
  rw [Functor.map_comp,hb] at hh
  have hh':=congrArg (fun z => d.hom≫z≫x) hh
  simpa only [Category.assoc,d.hom_inv_id_assoc] using hh'

private theorem y_detection_toda_source_iso_fixed_action
    {m n k l:ℤ} {X:Syn} (f:BiHom m n (S_0_0:Syn))
    (hf:∀a:Smn (Syn:=Syn) m n≅Smn m n,a.hom≫f=f)
    (x:BiHom k l X) (a:Smn (Syn:=Syn) (m+k) (n+l)≅Smn (m+k) (n+l)) :
    a.hom≫sphereAction f x=sphereAction f x := by
  exact y_detection_toda_source_iso_fixed_transport (SyntheticCategory.biShift (k,l))
    (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (k,l)) f hf
    ((SyntheticCategory.biShift_comp (m,n) (k,l)).app (S_0_0:Syn)).symm x a

private theorem y_detection_toda_eta_source_iso_fixed
    (unique : ∀ x y : BiHom 1 2 (S_0_0:Syn), x≠0 → y≠0 → x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (a:Smn (Syn:=Syn) 1 2≅Smn 1 2) :
    a.hom≫eta=eta := by
  by_cases he:eta=0
  · simp [he]
  apply unique _ _ ?_ he
  intro hh
  apply he
  have h:=congrArg (fun z => a.inv≫z) hh
  simpa only [←Category.assoc,a.inv_hom_id,Category.id_comp,comp_zero] using h

private theorem y_detection_toda_module_low_shuffle_exact
    (coh:BiShiftCoherence Syn)
    [IsTriangulated Syn]
    [(SyntheticCategory.biShift (Syn:=Syn) (123,129)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (123,129)).IsTriangulated]
    (unique:∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    {X:Syn} (a:BiHom 123 129 X) (ha:sphereAction h0 a=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda a h0 eta z) :
    sphereAction h0 z=sphereAction (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta) a := by
  let F:=SyntheticCategory.biShift (Syn:=Syn) (123,129)
  let G:=SyntheticCategory.biShift (Syn:=Syn) (1,3)
  let d:F.obj (Smn (Syn:=Syn) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
    F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:Syn)).symm ≪≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
  let J: (G⋙F)⋙shiftFunctor Syn (1:ℤ)≅SyntheticCategory.biShift (125,132):=
    Functor.isoWhiskerLeft (G⋙F) (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm ≪≫
      Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,3) (123,129))
        (SyntheticCategory.biShift (1,0)) ≪≫
          SyntheticCategory.biShift_comp (124,132) (1,0)
  let src: ((F.obj (G.obj (Smn (Syn:=Syn) 0 1)))⟦(1:ℤ)⟧)≅Smn 125 133 :=
    J.app (Smn 0 1) ≪≫ (SyntheticCategory.biShift_comp (0,1) (125,132)).app (S_0_0:Syn)
  let v:BiHom 2 4 (S_0_0:Syn):=sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta
  have hs:=y_detection_toda_module_low_shuffle_raw eta h0 hlow hind a ha z hz
  have hn:(F.map (G.map h0))⟦(1:ℤ)⟧'≫d.hom⟦(1:ℤ)⟧'≫
      (tripleTodaSource (Syn:=Syn) 1 2 0 1 123 129).inv≫z=src.hom≫sphereAction h0 z := by
    have he:=y_detection_toda_module_low_normalized_source coh
    change d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=Syn) 1 2 0 1 123 129).inv=J.hom.app (S_0_0:Syn) at he
    erw [reassoc_of% he]
    have hh:=J.hom.naturality h0
    dsimp only [Functor.comp_map] at hh
    erw [←Category.assoc,hh]
    change _ = (J.hom.app (Smn 0 1)≫(SyntheticCategory.biShift_comp (0,1) (125,132)).hom.app (S_0_0:Syn))≫
      (SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0:Syn)≫
        (SyntheticCategory.biShift (125,132)).map h0≫z
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
  have hs':
      (F.commShiftIso (1:ℤ)).inv.app (G.obj (Smn 0 1))≫
        F.map ((tripleTodaSource (Syn:=Syn) 0 1 1 2 0 1).inv≫v)≫a =
      -(src.hom≫sphereAction h0 z) := by
    simpa only [F,G,d,v,Preadditive.neg_comp,Category.assoc,hn] using hs
  let au:Smn (Syn:=Syn) 125 133≅Smn 125 133 :=
    src.symm ≪≫ ((F.commShiftIso (1:ℤ)).app (G.obj (Smn 0 1))).symm ≪≫
      F.mapIso (tripleTodaSource (Syn:=Syn) 0 1 1 2 0 1).symm ≪≫
        (SyntheticCategory.biShift_comp (2,4) (123,129)).app (S_0_0:Syn)
  have he:au.hom≫sphereAction v a=-(sphereAction h0 z) := by
    have hh:=congrArg (fun k => src.inv≫k) hs'
    simp only [Category.assoc,Preadditive.comp_neg,src.inv_hom_id_assoc,Functor.map_comp] at hh
    change (src.inv≫(F.commShiftIso (1:ℤ)).inv.app (G.obj (Smn 0 1))≫
      F.map ((tripleTodaSource (Syn:=Syn) 0 1 1 2 0 1).inv)≫
      (SyntheticCategory.biShift_comp (2,4) (123,129)).hom.app (S_0_0:Syn))≫
      (SyntheticCategory.biShift_comp (2,4) (123,129)).inv.app (S_0_0:Syn)≫F.map v≫a = _
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    exact hh
  have hv:∀aa:Smn (Syn:=Syn) 2 4≅Smn 2 4,aa.hom≫v=v := by
    intro aa
    exact y_detection_toda_source_iso_fixed_action eta (y_detection_toda_eta_source_iso_fixed unique eta) eta aa
  have hp:∀aa:Smn (Syn:=Syn) 125 133≅Smn 125 133,
      aa.hom≫sphereAction v a=sphereAction v a := by
    intro aa
    exact y_detection_toda_source_iso_fixed_action v hv a aa
  rw [hp au] at he
  let negIso:Smn (Syn:=Syn) 125 133≅Smn 125 133 :=
    ⟨-𝟙 _, -𝟙 _,by simp,by simp⟩
  have hneg:=hp negIso
  change (-𝟙 _)≫sphereAction v a=sphereAction v a at hneg
  simp only [Preadditive.neg_comp,Category.id_comp] at hneg
  exact ((congrArg Neg.neg he).trans (neg_neg _)).symm.trans hneg

open KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
universe uc
variable {C:Type uc} [StableHomotopyCategory.{uc,v} C] [HasFunctorialCofiber (C:=C)]
  [HasFunctorialCofiber (C:=Syn)] {H:Mod2EilenbergMacLane (C:=C)} {M:MilnorCooperations H}
omit [HasFunctorialCofiber (C := Syn)] in
private theorem y_detection_toda_shift_assoc_inv (coh : BiShiftCoherence Syn)
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

private theorem y_detection_toda_h0_action_lambda_three (D : AdamsComparison H M Syn)
    (η : BiHom 0 1 (S_0_0 : Syn))
    {X : Syn} (c : BiHom 123 132 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := y_detection_toda_shift_assoc_inv D.shiftCoherence (0,1) (123,132) (0,-3)
    (123,133) (123,129) (123,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (0,1) (123,132)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (123,132)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (123,132) (0,-3)).inv.naturality η)]
  rfl

private theorem y_detection_toda_eta_action_right_three (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    {X : Syn} (c : BiHom 123 132 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := y_detection_toda_shift_assoc_inv D.shiftCoherence (1,2) (123,132) (0,-3)
    (124,134) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (123,132)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (123,132) (0,-3)).inv.naturality η)]
  rfl

omit [HasFunctorialCofiber (C := Syn)] in
private theorem y_detection_toda_eta_double_action (coh:BiShiftCoherence Syn)
    (eta:BiHom 1 2 (S_0_0:Syn)) {X:Syn} (a:BiHom 123 129 X) :
    sphereAction (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta) a =
      sphereAction eta (sphereAction eta a) := by
  have ha:=y_detection_toda_shift_assoc_inv coh (1,2) (1,2) (123,129) (2,4) (124,131) (125,133)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:Syn)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at ha
  dsimp only [sphereProduct,sphereAction]
  simp only [Functor.map_comp,Category.assoc,Int.reduceAdd]
  erw [reassoc_of% ha]
  erw [←reassoc_of% ((SyntheticCategory.biShift_comp (1,2) (123,129)).inv.naturality eta)]
  rfl

private theorem y_detection_toda_main_toda_h0_relation (D:AdamsComparison H M Syn)
    (unique:∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    {X:Syn} (a:BiHom 123 132 X) (ha:lambdaMultiply 3 (sphereAction h0 a)=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda (lambdaMultiply 3 a) h0 eta z) :
    sphereAction h0 z=sphereAction eta (lambdaMultiply 3 (sphereAction eta a)) := by
  letI:=D.syntheticTriangulated
  letI:=D.shiftCommShift (123,129)
  letI:=D.shiftExact (123,129)
  have hh:sphereAction h0 (lambdaMultiply 3 a)=0 := (y_detection_toda_h0_action_lambda_three D h0 a).trans ha
  have he:=y_detection_toda_module_low_shuffle_exact D.shiftCoherence unique eta h0 hlow hind (lambdaMultiply 3 a) hh z hz
  rw [y_detection_toda_eta_double_action D.shiftCoherence,y_detection_toda_eta_action_right_three D] at he
  exact he

open KIP126.Algebra PageRepresentatives KIP126.SpectralSequence
variable {D:AdamsComparison H M Syn}
private theorem y_detection_toda_finite_sphere_outside_window_zero (BHS:EInftyComparison D)
    (q:ℕ) (hq:0<q) (s t w:ℤ) (hw:¬(0≤t-w ∧ t-w<q)) :
    IsZero (((D.family.quotient (S_0_0:Syn) q).sequence.ssData (s,t,w)).eInfty) := by
  let P:=BHS.presentation.finite SphereSpectrum q hq (s,t) w
  haveI : Subsingleton (finiteEInftyModel H SphereSpectrum q (s,t) w) := by
    dsimp only [finiteEInftyModel]
    rw [if_neg hw]
    infer_instance
  haveI : Subsingleton (((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
    P.injective.subsingleton
  let hn:=ModuleCat.isZero_of_subsingleton
    (((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
  let f:=(D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom q)).eInftyMap (s,t,w)
  let g:=(D.family.functor.map (XModLambdaN.map D.nu.unitIso.inv q)).eInftyMap (s,t,w)
  have hfg:g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem y_detection_toda_finite_sphere_filtration_floor (BHS:EInftyComparison D)
    (q:ℕ) (hq:0<q) (m w:ℤ) (N:ℕ) (hN:m+N≤w)
    (a:BiHom m w (XModLambdaN (S_0_0:Syn) q)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) N a := by
  have hfloor:FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 0 a := by
    refine ⟨a,?_⟩
    change a≫adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _=a
    rw [adamsTowerMap_self]
    exact Category.comp_id _
  apply ((D.quotientConvergence q hq).filtrationAtLeast_iff_of_eInfty_isZero 0 N m w
    (by omega) ?_ a).mp hfloor
  intro j hj hj'
  exact y_detection_toda_finite_sphere_outside_window_zero BHS q hq j (m+j) w (by omega)

private theorem y_detection_toda_lambda_filtration_preserved {A : Syn} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = _
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 s.toNat _ = a at hz
  dsimp only [lambdaMultiply]
  simp only [Category.assoc,hz]

private theorem y_detection_toda_main_toda_seventh_error_filtration (BHS:EInftyComparison D)
    (a3:BiHom 125 140 (XModLambdaN (S_0_0:Syn) 9)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (lambdaMultiply 7 a3) := by
  exact y_detection_toda_lambda_filtration_preserved 7 15 a3
    (y_detection_toda_finite_sphere_filtration_floor BHS 9 (by decide) 125 140 15 (by decide) a3)

private theorem y_detection_toda_family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
private theorem y_detection_toda_family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  rw [y_detection_toda_family_map_data,y_detection_toda_family_map_data,y_detection_toda_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
private theorem y_detection_toda_family_infinity_representative_map
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
  · rw [y_detection_toda_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])

private theorem y_detection_toda_detected_map
    (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
    (i : Tridegree) (x : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (ha : Detects (D.convergence X) i x a) :
    Detects (D.convergence Y) i (familyPageMap D.family f 2 i x) (a≫f) := by
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
  refine ⟨(D.family.functor.map f).eInftyMap i e,y_detection_toda_family_infinity_representative_map f i x e he,k a',?_,?_⟩
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
private theorem y_detection_toda_main_detects_of_difference
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

private theorem y_detection_toda_main_eta_right_three (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    {X : Syn} (c : BiHom 124 134 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := y_detection_toda_shift_assoc_inv D.shiftCoherence (1,2) (124,134) (0,-3)
    (125,136) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (124,134)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.naturality η)]
  rfl

private theorem y_detection_toda_main_eta_right_six (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    {X : Syn} (c : BiHom 124 137 X) :
    sphereAction η (lambdaMultiply 6 c) = lambdaMultiply 6 (sphereAction η c) := by
  have ha := y_detection_toda_shift_assoc_inv D.shiftCoherence (1,2) (124,137) (0,-6)
    (125,139) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (1,2) (124,137)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift (124,137)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,137) (0,-6)).inv.naturality η)]
  rfl

private theorem y_detection_toda_main_lambda_six_one (D : AdamsComparison H M Syn)
    {X:Syn} (c : BiHom 125 140 X) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  have ha := y_detection_toda_shift_assoc_inv D.shiftCoherence (125,140) (0,-1) (0,-6)
    (125,139) (0,-7) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (125,140) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 125 140)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 6 7 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl

private theorem y_detection_toda_main_toda_h0_error_formula (D:AdamsComparison H M Syn)
    (unique:∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    (U:E2 H SphereSpectrum 10 134) (V:E2 H SphereSpectrum 9 132)
    (a11:BiHom 123 132 (XModLambdaN (S_0_0:Syn) 11))
    (ha:AlphaOneProperties D eta h0 U V a11)
    (u:BiHom 124 134 (S_0_0:Syn)) (hu:SphereDetected D 10 134 0 U u)
    (z:BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (hz:ModuleTripleToda (lambdaMultiply 3 (a11≫(D.quotientTower S_0_0).rho 9 11 (by decide))) h0 eta z) :
    ∃a3:BiHom 125 140 (XModLambdaN (S_0_0:Syn) 9),
      sphereAction h0 z=(show BiHom 125 133 (XModLambdaN (S_0_0:Syn) 9) from
        quotientClass 9 (lambdaMultiply 3 (sphereProduct eta u)))+
        (show BiHom 125 133 (XModLambdaN (S_0_0:Syn) 9) from lambdaMultiply 7 a3) := by
  obtain ⟨a2,a3,hr,he⟩:=ha.2.2.1 u hu
  refine ⟨a3,?_⟩
  rw [y_detection_toda_main_toda_h0_relation D unique eta h0 hlow hind _ ha.2.2.2 z hz,hr]
  have hadd (v w:BiHom 124 131 (XModLambdaN (S_0_0:Syn) 9)):
      sphereAction eta (v+w)=sphereAction eta v+sphereAction eta w := by
    simp only [sphereAction,Preadditive.comp_add]
  rw [hadd,y_detection_toda_main_eta_right_three D,y_detection_toda_main_eta_right_six D,he,y_detection_toda_main_lambda_six_one D]
  congr 1
  simp only [quotientClass,sphereProduct,sphereAction,lambdaMultiply,Category.assoc]

private theorem y_detection_toda_main_toda_h0_detected_weak (D:AdamsComparison H M Syn)
    (BHS:EInftyComparison D)
    (unique:∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    (U:E2 H SphereSpectrum 10 134) (V:E2 H SphereSpectrum 9 132) (T:E2 H SphereSpectrum 14 139)
    (a11:BiHom 123 132 (XModLambdaN (S_0_0:Syn) 11))
    (ha:AlphaOneProperties D eta h0 U V a11)
    (u:BiHom 124 134 (S_0_0:Syn)) (hu:SphereDetected D 10 134 0 U u)
    (hc5:Detects D.sphereConvergence (14,139,133) (D.sphereE2 14 139 6 T)
      (lambdaMultiply 3 (sphereProduct eta u)))
    (z:BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (hz:ModuleTripleToda (lambdaMultiply 3 (a11≫(D.quotientTower S_0_0).rho 9 11 (by decide))) h0 eta z) :
    Detects (D.quotientConvergence 9 (by decide)) (14,139,133) (D.quotientLabel 9 14 139 6 T)
      (sphereAction h0 z) := by
  have hd:=y_detection_toda_detected_map (D:=D) .sphere (.quotient 9 .sphere) (XModLambdaN.incl (S_0_0:Syn) 9)
    (14,139,133) (D.sphereE2 14 139 6 T) _ hc5
  obtain ⟨a3,he⟩:=y_detection_toda_main_toda_h0_error_formula D unique eta h0 hlow hind U V a11 ha u hu z hz
  apply y_detection_toda_main_detects_of_difference (D.quotientConvergence 9 (by decide)) (14,139,133) hd
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
    ((show BiHom 125 133 (XModLambdaN (S_0_0:Syn) 9) from sphereAction h0 z)-
      (show BiHom 125 133 (XModLambdaN (S_0_0:Syn) 9) from quotientClass 9 (lambdaMultiply 3 (sphereProduct eta u))))
  rw [he,add_sub_cancel_left]
  exact y_detection_toda_main_toda_seventh_error_filtration BHS a3

private theorem y_detection_toda_sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (y_detection_toda_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (y_detection_toda_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (y_detection_toda_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel

private theorem y_detection_toda_sphere_finite_detection_nonzero
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
  have henu := y_detection_toda_family_infinity_representative_map (D:=D) g (s,t,t-k) _ _ he
  change HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
    (familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x)) ((D.family.functor.map g).eInftyMap (s,t,t-k) e) at henu
  rw [y_detection_toda_sphere_quotient_label_to_nu (D:=D) q k s t x,he0,map_zero] at henu
  have hh := (BHS.labels.1 .sphere q hq (s,t) k hk ⟨x,hx⟩ 0).mp henu
  rw [map_zero] at hh
  exact hn ((NestedQuotient.projection_eq_zero ⟨x,hx⟩).mp hh.symm)

private theorem y_detection_toda_survives_twelve_not_boundary_eleven (X : C) (p : ℤ × ℤ)
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
private theorem y_detection_toda_choice_represents_unique {a b : E.Page r p}
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

private theorem y_detection_toda_choice_next_projection_zero_iff_incoming
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

private theorem y_detection_toda_choice_next_nonzero_of_not_hit
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
  have heb : br=b := y_detection_toda_choice_represents_unique hbr hb
  intro ha0
  have hv := y_detection_toda_choice_next_projection_zero_iff_incoming E r hr0 q
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

private theorem y_detection_toda_choice_permanent_survives_of_no_early_hit
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
      have han := y_detection_toda_choice_next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h

private theorem y_detection_toda_choice_nonzero_differential_not_zero
    (h : HasNonzeroDifferential E r p q x y)
    (hzero : HasDifferential E r p q x 0) : False := by
  obtain ⟨he,a,b,ha,hb,hd,hbn⟩ := h
  obtain ⟨he',a',b',ha',hb',hd'⟩ := hzero
  have haa : a=a' := y_detection_toda_choice_represents_unique ha ha'
  have hbb : b'=0 := y_detection_toda_choice_represents_unique hb' (RepresentsOnPage.zero hb'.1)
  apply hbn
  calc b = (E.d r p ≫ eqToHom (congrArg (E.Page r) he)) a := hd.symm
       _ = b' := by simpa only [haa] using hd'
       _ = 0 := hbb

end MainTodaCycles
open KIP126.Computation.SphereAndCofiber MainTodaCycles
variable {L:SphereAdamsClasses H} {G:TmfDetectionClasses H}
private theorem y_detection_toda_target_survives_twelve_of_d6_vanishes
    (I:AdamsComputationTheorems D L G) (SF:Derived.SphereFacts I.interpretation) (hc3:Stem126D6Vanishes L) :
    SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) := by
  have labels:=distinguished_expression_comparisons I
  have hp:=SF.t_permanent_cycle
  rw [labels.2.2] at hp
  have hn:L.target M≠0 := by
    intro hz
    apply SF.t_not_h0_multiple
    refine ⟨0,?_⟩
    rw [labels.2.2,hz]
    simp only [Sphere.Internal.product,map_zero]
  apply y_detection_toda_choice_permanent_survives_of_no_early_hit (by change (2:ℤ)≤2; decide) 12 (by decide) hp hn
  intro r hr hr12 hit
  rw [←labels.2.2] at hit
  rcases SF.t_only_incoming r hit with ⟨he,hd⟩|⟨he,_⟩
  · subst r
    change HasNonzeroDifferential (sequence D .sphere) 6 (8,134) (14,139)
      (I.interpretation.sphere 8 134 KIP126.Computation.Near126.W)
      (I.interpretation.sphere 14 139 KIP126.Computation.Near126.T) at hd
    rw [labels.1,labels.2.2] at hd
    exact y_detection_toda_choice_nonzero_differential_not_zero hd hc3
  · omega

private theorem y_detection_toda_main_toda_h0_detected_nonzero (D:AdamsComparison H M Syn)
    (I:AdamsComputationTheorems D L G) (SF:Derived.SphereFacts I.interpretation) (BHS:EInftyComparison D)
    (unique:∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:Syn)) (h0:BiHom 0 1 (S_0_0:Syn))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:Syn),sphereProduct h0 a=0)
    (V:E2 H SphereSpectrum 9 132)
    (hc3:Stem126D6Vanishes L) (hc5:EtaExtensionDetection M D.toAdamsComparisonData L eta)
    (a11:BiHom 123 132 (XModLambdaN (S_0_0:Syn) 11))
    (ha:AlphaOneProperties D eta h0 (L.U M) V a11)
    (z:BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (hz:ModuleTripleToda (lambdaMultiply 3 (a11≫(D.quotientTower S_0_0).rho 9 11 (by decide))) h0 eta z) :
    FiniteDetected D 9 (by decide) 14 139 6 (L.target M) (sphereAction h0 z) := by
  obtain ⟨u,hu,hc5⟩:=hc5
  have hd:=y_detection_toda_main_toda_h0_detected_weak D BHS unique eta h0 hlow hind (L.U M) V (L.target M)
    a11 ha u hu hc5 z hz
  have hp:=SF.t_permanent_cycle
  rw [(distinguished_expression_comparisons I).2.2] at hp
  apply y_detection_toda_sphere_finite_detection_nonzero BHS 9 6 (by decide) (by decide) 14 139 (L.target M) ?_ ?_ _ hd
  · exact permanentCycles_le_cycles H SphereSpectrum (14,139) _ hp
  · intro hb
    apply y_detection_toda_survives_twelve_not_boundary_eleven SphereSpectrum (14,139) (L.target M)
      (y_detection_toda_target_survives_twelve_of_d6_vanishes I SF hc3)
    exact boundaries_monotone H SphereSpectrum (14,139) (by decide) hb

end KIP126.Main.SectionSeven

namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}

open KIP126.Literature.AdamsSynthetic

private theorem y_detection_exact_target_sphere_first_label_transport (s t : ℤ)
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

private theorem y_detection_exact_target_sphere_permanent_first_quotient_lift
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
  exact y_detection_exact_target_sphere_first_label_transport s t x

private theorem y_detection_exact_target_vanishes_mod_lambda_iff_multiple
    (n : ℕ) {X : Syn} (m w : ℤ) (z : BiHom m (w-(n:ℤ)) X) :
    VanishesModLambda n z ↔ ∃ b : BiHom m w X, lambdaMultiply n b=z := by
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

private theorem y_detection_exact_target_map_filtration {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
    (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
  obtain ⟨z,hz⟩ := hx
  refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
  change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
    adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
  rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
  rfl

omit [HasFunctorialCofiber (C := Syn)] in
private theorem y_detection_exact_target_shift_assoc_inv (coh : BiShiftCoherence Syn)
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

private theorem y_detection_exact_target_lambda_six_one (D : AdamsComparison H M Syn)
    (c : BiHom 125 140 (S_0_0 : Syn)) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  have ha := y_detection_exact_target_shift_assoc_inv D.shiftCoherence (125,140) (0,-1) (0,-6)
    (125,139) (0,-7) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (125,140) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 125 140)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 6 7 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl

private theorem y_detection_exact_target_sphere_exact_target_split
    (BHS : SyntheticComparisonTheorems D) (T : E2 H SphereSpectrum 14 139)
    (hT : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (14,139) T)
    (a : BiHom 125 133 (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (14,139,133) (D.sphereE2 14 139 6 T) a) :
    ∃ t : BiHom 125 139 (S_0_0 : Syn),
      D.sphereFirstQuotient 14 139 (quotientClass 1 t)=T ∧ lambdaMultiply 6 t=a := by
  obtain ⟨t00,ht0⟩ := y_detection_exact_target_sphere_permanent_first_quotient_lift BHS 14 139 T hT
  let t0 : BiHom 125 139 (S_0_0 : Syn) := t00
  change D.sphereFirstQuotient 14 139 (quotientClass 1 t0)=T at ht0
  let a0 : BiHom 125 133 (S_0_0 : Syn) := lambdaMultiply 6 t0
  have ha0 : Detects D.sphereConvergence (14,139,133) (D.sphereE2 14 139 6 T) a0 := by
    have h := D.comparisonCompatible.homotopy_lambda 14 139 6 t0
    rw [ht0] at h
    exact h
  have hdiff : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a-a0) :=
    detects_sub_filtration D.sphereConvergence (14,139,133) ha ha0
  have hnu := y_detection_exact_target_map_filtration (D:=D) D.nu.unitIso.inv (a-a0) hdiff
  have hlam := BHS.filtration_lambda .sphere 125 133 15 (by omega) ((a-a0)≫D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 ((a-a0)≫D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 7 b=(a-a0)≫D.nu.unitIso.inv at hlam
  obtain ⟨b,hb⟩ := hlam.mp hnu
  let c : BiHom 125 140 (S_0_0 : Syn) := b≫D.nu.unitIso.hom
  have hc : lambdaMultiply 7 c=a-a0 := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun x=>x≫D.nu.unitIso.hom) hb
  let lc : BiHom 125 139 (S_0_0 : Syn) := lambdaMultiply 1 c
  have hq : quotientClass 1 lc=0 := by
    exact (y_detection_exact_target_vanishes_mod_lambda_iff_multiple 1 125 140 lc).mpr ⟨c,rfl⟩
  refine ⟨t0+lc,?_,?_⟩
  · change D.sphereFirstQuotient 14 139 ((t0+lc)≫XModLambdaN.incl _ 1)=T
    rw [Preadditive.add_comp,map_add]
    change D.sphereFirstQuotient 14 139 (quotientClass 1 t0)+
      D.sphereFirstQuotient 14 139 (quotientClass 1 lc)=T
    rw [ht0,hq,map_zero,add_zero]
  · let c7 : BiHom 125 133 (S_0_0 : Syn) := lambdaMultiply 7 c
    have he1 : (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 lc)=c7 :=
      y_detection_exact_target_lambda_six_one D c
    have he : (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 (t0+lc))=a0+c7 := by
      calc
        _ = a0+(show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 lc) := by
          simp only [a0,lambdaMultiply,Preadditive.comp_add]
        _ = a0+c7 := by rw [he1]
    change (show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 (t0+lc))=a
    rw [he]
    have hc7 : c7=a-a0 := hc
    rw [hc7]
    abel

end
end KIP126.Main.SectionSeven
namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven KIP126.Computation.SphereAndCofiber
open KIP126.Literature.AdamsSynthetic KIP126.Algebra PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem anyy_seventh_error_zero
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (a : BiHom 125 140 (XModLambdaN (S_0_0 : Syn) 9)) :
    lambdaMultiply 7 a = 0 := by
  have hf := y_detection_toda_finite_sphere_filtration_floor BHS.eInfty 9
    (by decide) 125 140 15 (by decide) a
  have hf' := y_detection_toda_lambda_filtration_preserved 1 15 a hf
  have hz := y_detection_page_lambda_six_filtration_fifteen_zero I BHS.eInfty
    R (lambdaMultiply 1 a) hf'
  rw [y_detection_toda_main_lambda_six_one D] at hz
  exact hz

private theorem anyy_lambda_zero (D : AdamsComparison H M Syn) {X : Syn}
    (x : BiHom 125 139 X) : lambdaMultiply 0 x = x := by
  have hc := D.shiftCoherence.right_unit (125,139) (S_0_0 : Syn)
  have he : (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : Syn) =
      SyntheticCategory.biShift_zero.hom.app (Smn 125 139 : Syn) := by
    change (biShiftAddIso (125,139) (0,0) (125,139) (by simp)).hom.app _ = _ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (125,139) (0,0)).inv.app (S_0_0 : Syn) ≫
    (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : Syn) ≫ x = x
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

private theorem anyy_detected_ne_zero
    {F : SyntheticAdamsFamily Syn} {A X : Syn} {unit : S_0_0 ⟶ A}
    (c : TowerConvergence unit F X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : DetectsNonzero c i x a) : a ≠ 0 := by
  obtain ⟨⟨e,he,b,hb,hgr⟩,e',he',hne⟩ := ha
  intro hzero
  have hb0 : b=0 := by
    apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono
      ((towerFiltration unit X).F i.1 (i.2.1-i.1,i.2.2)).arrow)
    rw [hb,hzero,map_zero]
  have he0 : e=0 := by
    apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (c.identification i).hom)
    rw [hgr,hb0,map_zero,map_zero]
  exact hne ((he.unique he').symm.trans he0)

private theorem anyy_bracket_exact_target
    (I : AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation) (BHS : SyntheticComparisonTheorems D)
    (R : RealizationDetectionData D)
    (unique : ∀ x y : BiHom 1 2 (S_0_0 : Syn), x≠0 → y≠0 → x=y)
    (eta : BiHom 1 2 (S_0_0 : Syn)) (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hlow : TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct h0 a=0)
    (V : E2 H SphereSpectrum 9 132)
    (hc3 : Stem126D6Vanishes L) (hc5 : EtaExtensionDetection M D.toAdamsComparisonData L eta)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : AlphaOneProperties D eta h0 (L.U M) V a11)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hz : ModuleTripleToda (lambdaMultiply 3
      (a11≫(D.quotientTower S_0_0).rho 9 11 (by decide))) h0 eta z) :
    ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9),
      FiniteDetected D 9 (by decide) 14 139 0 (L.target M) t ∧
      sphereAction h0 z=lambdaMultiply 6 t ∧ lambdaMultiply 6 t≠0 := by
  have hzdet := y_detection_toda_main_toda_h0_detected_nonzero D I SF BHS.eInfty
    unique eta h0 hlow hind V hc3 hc5 a11 ha z hz
  obtain ⟨u,hu,hcu⟩ := hc5
  have hp := SF.t_permanent_cycle
  rw [(distinguished_expression_comparisons I).2.2] at hp
  obtain ⟨t,ht,he⟩ := y_detection_exact_target_sphere_exact_target_split BHS (L.target M) hp
    (lambdaMultiply 3 (sphereProduct eta u)) hcu
  have htd := D.comparisonCompatible.homotopy_lambda 14 139 0 t
  rw [ht,anyy_lambda_zero D] at htd
  have htq := y_detection_toda_detected_map (D:=D) .sphere (.quotient 9 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 9) (14,139,139) _ _ htd
  have htn : FiniteDetected D 9 (by decide) 14 139 0 (L.target M) (quotientClass 9 t) := by
    apply y_detection_toda_sphere_finite_detection_nonzero BHS.eInfty 9 0 (by decide)
      (by decide) 14 139 (L.target M) ?_ ?_ _ htq
    · exact permanentCycles_le_cycles H SphereSpectrum (14,139) _ hp
    · intro hb
      apply y_detection_toda_survives_twelve_not_boundary_eleven SphereSpectrum (14,139)
        (L.target M) (y_detection_toda_target_survives_twelve_of_d6_vanishes I SF hc3)
      exact boundaries_monotone H SphereSpectrum (14,139) (by decide) hb
  obtain ⟨a3,hformula⟩ := y_detection_toda_main_toda_h0_error_formula D unique eta h0 hlow hind
    (L.U M) V a11 ha u hu z hz
  have heq : sphereAction h0 z=lambdaMultiply 6 (quotientClass 9 t) := by
    rw [anyy_seventh_error_zero I BHS R a3,add_zero,←he] at hformula
    simpa only [lambdaMultiply,quotientClass,Category.assoc] using hformula
  refine ⟨quotientClass 9 t,htn,heq,?_⟩
  rw [←heq]
  exact anyy_detected_ne_zero (D.quotientConvergence 9 (by decide)) (14,139,133) hzdet

open KIP126.LinE2 KIP126.Algebra
private theorem anyy_lambda_one_division_of_quotient_zero
    {X : Syn} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
    ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
  obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors 1 z).mp hz
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  let e : F.obj (Smn m w : Syn) ≅ Smn m (w-1) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).preimage (e.hom≫a)
  have hb : F.map b=e.hom≫a :=
    (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_preimage _
  refine ⟨b,?_⟩
  have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
    unfold lambdaMultiply
    change eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
      lambdaPow 1 (Smn m w) ≫ b =
      (eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
      lambdaPow 1 (Smn m w) ≫ b
    exact (Category.assoc _ _ _).symm
  rw [he]
  rw [←lambdaPow_naturality 1 b]
  change e.inv≫F.map b≫lambdaPow 1 X=z
  rw [hb]
  simp only [Category.assoc,e.inv_hom_id_assoc]
  exact ha
private theorem anyy_sphere_one_three_zero {D : AdamsComparison H M Syn} (BHS : EInftyComparison D)
    (V : SphereVanishingLine H) (h23 : Subsingleton (E2 H SphereSpectrum 2 3))
    (z : BiHom 1 3 (S_0_0 : Syn)) : z=0 := by
  have hsep := D.homotopySeparated .sphere 1 3
  refine (D.convergence .sphere).eq_zero_of_eInfty_isZero_ge 0 1 3 hsep ?_ z ?_
  · intro j hj
    let i : Tridegree := (j,1+j,3)
    let P := BHS.presentation.nu SphereSpectrum ((j:ℤ),1+j) 3
    haveI : Subsingleton (PageRepresentatives.nuEInftyModel H SphereSpectrum ((j:ℤ),1+j) 3) := by
      dsimp only [PageRepresentatives.nuEInftyModel]
      split_ifs with h
      · have hs : Subsingleton (E2 H SphereSpectrum j (1+j)) := by
          by_cases he : j=2
          · subst j; exact h23
          · exact V _ _ (by omega) (by omega)
        letI : Subsingleton (PageRepresentatives.permanentCycles H SphereSpectrum ((j:ℤ),1+j)) :=
          ⟨fun a b => Subtype.ext (hs.elim _ _)⟩
        refine ⟨?_⟩
        rintro ⟨a⟩ ⟨b⟩
        exact congrArg (NestedQuotient.projection _ _) (Subsingleton.elim a b)
      · infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro e
    have he : (D.family.functor.map D.nu.unitIso.inv).eInftyMap i e=0 :=
      P.injective (Subsingleton.elim _ _)
    have hh := congrArg (fun a => (D.family.functor.map D.nu.unitIso.hom).eInftyMap i a) he
    change ((D.family.functor.map D.nu.unitIso.inv).eInftyMap i ≫
      (D.family.functor.map D.nu.unitIso.hom).eInftyMap i) e=_ at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
    simpa only [ConcreteCategory.id_apply,map_zero] using hh
  · change ∃a,towerHomotopyMap (nuCoefficientUnit H.unit D.nu)
      (S_0_0:Syn) 0 (1,3) a=z
    refine ⟨z,?_⟩
    change _≫adamsTowerMap (nuCoefficientUnit H.unit D.nu) (S_0_0:Syn) 0 0 _=_
    rw [adamsTowerMap_self]
    exact Category.comp_id _
private theorem anyy_eta_first_quotient_injective {D : AdamsComparison H M Syn} (BHS : EInftyComparison D)
    (V : SphereVanishingLine H) (h23 : Subsingleton (E2 H SphereSpectrum 2 3)) :
    Function.Injective (fun z : BiHom 1 2 (S_0_0:Syn) => quotientClass 1 z) := by
  intro x y h
  have hz : quotientClass 1 (x-y)=0 := by
    simp only [quotientClass,Preadditive.sub_comp] at h ⊢
    rw [h,sub_self]
  obtain ⟨b,hb⟩ := anyy_lambda_one_division_of_quotient_zero 1 3 (x-y) hz
  rw [anyy_sphere_one_three_zero BHS V h23 b] at hb
  simp only [lambdaMultiply,comp_zero] at hb
  exact sub_eq_zero.mp hb.symm
private theorem anyy_eta_unique_from_low_degrees {D : AdamsComparison H M Syn} (BHS : EInftyComparison D)
    (V:SphereVanishingLine H)
    (eta_nonzero_unique : ∀ x y : E2 H SphereSpectrum 1 2, x ≠ 0 → y ≠ 0 → x = y)
    (h23 : Subsingleton (E2 H SphereSpectrum 2 3)) :
    ∀x y:BiHom 1 2 (S_0_0:Syn),x≠0 → y≠0 → x=y := by
  have hi:=anyy_eta_first_quotient_injective BHS V h23
  let f:=fun z:BiHom 1 2 (S_0_0:Syn)=>D.sphereFirstQuotient 1 2 (quotientClass 1 z)
  have hf:Function.Injective f:=(D.sphereFirstQuotient 1 2).injective.comp hi
  intro x y hx hy
  have hn (z:BiHom 1 2 (S_0_0:Syn)) (hz:z≠0) : f z≠0 := by
    intro hh
    apply hz
    apply hf
    simpa only [f,quotientClass,zero_comp,map_zero] using hh
  apply hf
  exact eta_nonzero_unique _ _ (hn x hx) (hn y hy)

end KIP126.Main.SectionSeven
