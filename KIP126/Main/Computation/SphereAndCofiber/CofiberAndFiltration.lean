module

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
public import KIP126.Main.Computation.SphereAndCofiber.Stem125Vanishing

/-! Stable cofiber conclusions, label comparisons and filtration separation. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
section CnuDifferential
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
local notation "E" => sequence D KIP126.Computation.SphereAndCofiber.Raw.Spectrum.nuCofiber

/-- A common representative on page at least three is a d₂ cycle. -/
private theorem cnu_d2_zero_of_reaches (r : ℤ) (hr : 3 ≤ r)
    (x : (E).Page 2 (9,135)) (hx : ReachesPage E r (9,135) x) :
    (E).d 2 (9,135) x = 0 := by
  obtain ⟨xr, hr', z, hz, _⟩ := hx
  change x ∈ LinearMap.ker ((E).d 2 (9,135)).hom
  rw [← subobjectModule_kernel, (E).Z_succ 2 (9,135) (by change (2 : ℤ) ≤ 2; omega), subobjectModule_image]
  let A := (E).ssData (9,135)
  have hle : (1 : WithTop ℕ) ≤ ↑(r-2).toNat := by
    exact_mod_cast (show 1 ≤ (r-2).toNat by omega)
  refine ⟨(Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) (A.Z_anti hle)) z, ?_⟩
  change (Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0)
    ((Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) _) z) = x
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz

/-- The complete five-element degree-(9,135) basis gives the whole d₂ map. -/
private theorem cnu_d2_decode (I : AdamsComputationTheorems D L G) (i : Fin 5) : I.interpretation.coordinateSum .nuCofiber 9 135 [i.val] =
    some (I.interpretation.basis .nuCofiber 9 135 i.val) := by
  have hv : Raw.coordinatesValid Raw.degrees .nuCofiber 9 135 [i.val] = true := by
    fin_cases i <;> decide
  simp [E2Interpretation.coordinateSum, hv]

private theorem cnu_d2_target (p q : ℤ × ℤ) (x : (E).Page 2 p) (y : (E).Page 2 q)
    (h : HasDifferential E 2 p q x y) : (E).d 2 q y = 0 := by
  obtain ⟨rfl, hd⟩ := h.eq_on_page_two
  have hd' : (E).d 2 p x = y := by
    simpa only [eqToHom_refl, Category.comp_id] using hd
  exact IsPageBoundary.d_eq_zero (r := 2) (p := p) ⟨x, hd'⟩

private theorem cnu_d2_zero_h0 (I : AdamsComputationTheorems D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 0) = 0 := by
  classical
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 51) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hx' : x = I.interpretation.basis .nuCofiber 9 135 0 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨0, by decide⟩))
  subst x
  obtain ⟨_, xr, yr, hxr, _, _⟩ := h
  exact cnu_d2_zero_of_reaches 3 (by decide) _ ⟨xr, hxr⟩

private theorem cnu_d2_zero_h1 (I : AdamsComputationTheorems D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 1) = 0 := by
  classical
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 49) (by rfl))
  obtain ⟨x, hx, h⟩ := hrow
  have hx' : x = I.interpretation.basis .nuCofiber 9 135 1 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨1, by decide⟩))
  subst x
  exact cnu_d2_zero_of_reaches 16 (by decide) _ h

private theorem cnu_d2_zero_h2 (I : AdamsComputationTheorems D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 2) = 0 := by
  classical
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 50) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hx' : x = I.interpretation.basis .nuCofiber 9 135 2 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨2, by decide⟩))
  subst x
  obtain ⟨_, xr, yr, hxr, _, _⟩ := h
  exact cnu_d2_zero_of_reaches 4 (by decide) _ ⟨xr, hxr⟩

private theorem cnu_d2_zero_h3 (I : AdamsComputationTheorems D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 3) = 0 := by
  classical
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 47) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hy' : y = I.interpretation.basis .nuCofiber 9 135 3 :=
    Option.some.inj (hy.symm.trans (cnu_d2_decode I ⟨3, by decide⟩))
  subst y
  exact cnu_d2_target (7,134) (9,135) x _ h

private theorem cnu_d2_zero_h4 (I : AdamsComputationTheorems D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 4) = 0 := by
  classical
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 48) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hy' : y = I.interpretation.basis .nuCofiber 9 135 4 :=
    Option.some.inj (hy.symm.trans (cnu_d2_decode I ⟨4, by decide⟩))
  subst y
  exact cnu_d2_target (7,134) (9,135) x _ h

private theorem cnu_d2_zero (I : AdamsComputationTheorems D L G) : (E).d 2 (9,135) = 0 := by
  have h0 : (E).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 0) = 0 := cnu_d2_zero_h0 I
  have h1 : (E).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 1) = 0 := cnu_d2_zero_h1 I
  have h2 : (E).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 2) = 0 := cnu_d2_zero_h2 I
  have h3 : (E).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 3) = 0 := cnu_d2_zero_h3 I
  have h4 : (E).d 2 (9,135) (I.interpretation.basis .nuCofiber 9 135 4) = 0 := cnu_d2_zero_h4 I
  have hb := I.basis _ (List.mem_of_getElem? (i := 34) (by rfl))
  obtain ⟨e, he⟩ := hb
  change (E).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 9 135 i.val at he
  have hone (i : Fin 5) : (E).d 2 (9,135) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he i]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hall (f : Fin 5 →₀ KIP126.Algebra.F2) : (E).d 2 (9,135) (e.symm f) = 0 := by
    induction f using Finsupp.induction with
    | zero => simp
    | @single_add i a f hi ha ih =>
      rw [map_add, map_add, ih, add_zero]
      fin_cases a
      · simp
      · exact hone i
  ext x
  simpa only [LinearEquiv.symm_apply_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hall (e x)


/-- Add actual common cycle representatives, before quotienting on either page. -/
private theorem represents_add
    {R : Type*} [Ring R] {ESeq : KIP126.SpectralSequence (ModuleCat R) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {x y : ESeq.Page 2 p} {xr yr : ESeq.Page r p}
    (hx : RepresentsOnPage ESeq r p x xr) (hy : RepresentsOnPage ESeq r p y yr) :
    RepresentsOnPage ESeq r p (x+y) (xr+yr) := by
  obtain ⟨hr, zx, hx, hxr⟩ := hx
  obtain ⟨_, zy, hy, hyr⟩ := hy
  exact ⟨hr, zx+zy, by rw [map_add, hx, hy], by rw [map_add, hxr, hyr]⟩

private theorem differential_add
    {R : Type*} [Ring R] {ESeq : KIP126.SpectralSequence (ModuleCat R) (ℤ × ℤ)}
    {r : ℤ} {p q : ℤ × ℤ} {x x' : ESeq.Page 2 p} {y y' : ESeq.Page 2 q}
    (h : HasDifferential ESeq r p q x y) (h' : HasDifferential ESeq r p q x' y') :
    HasDifferential ESeq r p q (x+x') (y+y') := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  obtain ⟨_, xr', yr', hx', hy', hd'⟩ := h'
  exact ⟨hdeg, xr+xr', yr+yr', represents_add hx hx', represents_add hy hy',
    by rw [map_add, hd, hd']⟩

/-- Unchanged boundaries preserve nonzero common representatives. -/
private theorem page_projection_nonzero
    {R : Type*} [Ring R] (A : SSData (ModuleCat R))
    (n m : WithTop ℕ) (hnm : n ≤ m) (hB : A.B m = A.B n)
    (z : (Subobject.underlying.obj (A.Z m) : ModuleCat R))
    (hne : (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z ≠ 0) :
    A.pageπ m z ≠ 0 := by
  intro hz
  have hmem := (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z m) z).mp hz
  apply hne
  rw [hB] at hmem
  change A.pageπ n ((Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) z) = 0
  apply (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z n) _).mpr
  change (Subobject.ofLE (A.Z m) (A.Z n) _ ≫ (A.Z n).arrow) z ∈ _
  rwa [Subobject.ofLE_arrow]


/-- Source [0,3,4] is the sum of the three Cnu source rows; the target is
bottom-cell [3].  The top/bottom identifications remain the fields of I,
so the later Mahowald application uses exactly D.hopfAndDetector.nuMap. -/
theorem cnu_d3 (I : AdamsComputationTheorems D L G) : Derived.CnuDifferential I.interpretation := by
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.interpretation.coordinateSum .nuCofiber s t indices =
        some ((indices.map (I.interpretation.basis .nuCofiber s t)).sum) := by
    simp only [E2Interpretation.coordinateSum, hv, ite_true]
  obtain ⟨x0, hx0, y0, hy0, h0⟩ :=
    I.adamsStatements _ (List.mem_of_getElem? (i := 657) (by rfl))
  obtain ⟨x3, hx3, y3, hy3, h3⟩ :=
    I.adamsStatements _ (List.mem_of_getElem? (i := 34) (by rfl))
  obtain ⟨x4, hx4, y4, hy4, h4⟩ :=
    I.adamsStatements _ (List.mem_of_getElem? (i := 33) (by rfl))
  change Page D .nuCofiber 8 134 at x0 x3 x4
  change Page D .nuCofiber 11 136 at y0 y3 y4
  change HasDifferential E 3 (8,134) (11,136) x0 y0 at h0
  change HasDifferential E 3 (8,134) (11,136) x3 y3 at h3
  change HasDifferential E 3 (8,134) (11,136) x4 y4 at h4
  have hx0' : x0 = I.interpretation.basis .nuCofiber 8 134 0 := by
    have h := Option.some.inj (hx0.symm.trans (hdecode 8 134 [0] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hx3' : x3 = I.interpretation.basis .nuCofiber 8 134 3 := by
    have h := Option.some.inj (hx3.symm.trans (hdecode 8 134 [3] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hx4' : x4 = I.interpretation.basis .nuCofiber 8 134 4 := by
    have h := Option.some.inj (hx4.symm.trans (hdecode 8 134 [4] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hy0' : y0 = I.interpretation.basis .nuCofiber 11 136 1 +
      I.interpretation.basis .nuCofiber 11 136 2 + I.interpretation.basis .nuCofiber 11 136 3 := by
    have h := Option.some.inj (hy0.symm.trans (hdecode 11 136 [1,2,3] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc] using h
  have hy3' : y3 = I.interpretation.basis .nuCofiber 11 136 2 := by
    have h := Option.some.inj (hy3.symm.trans (hdecode 11 136 [2] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hy4' : y4 = I.interpretation.basis .nuCofiber 11 136 1 := by
    have h := Option.some.inj (hy4.symm.trans (hdecode 11 136 [1] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  obtain ⟨e, he⟩ := I.basis _ (List.mem_of_getElem? (i := 43) (by rfl))
  change (E).Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 11 136 i.val at he
  have htwo (y : (E).Page 2 (11,136)) : y+y = 0 := by
    apply e.injective
    rw [map_add, map_zero]
    ext i
    exact CharTwo.add_self_eq_zero ((e y) i)
  have hne : I.interpretation.basis .nuCofiber 11 136 3 ≠ 0 := by
    rw [← he ⟨3, by decide⟩]
    intro hz
    have h := congrArg e hz
    simp only [LinearEquiv.apply_symm_apply, map_zero] at h
    change (Finsupp.single (⟨3, by decide⟩ : Fin 5) (1 : KIP126.Algebra.F2)) = 0 at h
    exact Finsupp.single_ne_zero.mpr one_ne_zero h
  have hsum : y0+y3+y4 = I.interpretation.basis .nuCofiber 11 136 3 := by
    rw [hy0', hy3', hy4']
    calc
      _ = (I.interpretation.basis .nuCofiber 11 136 1 + I.interpretation.basis .nuCofiber 11 136 1) +
          (I.interpretation.basis .nuCofiber 11 136 2 + I.interpretation.basis .nuCofiber 11 136 2) +
          I.interpretation.basis .nuCofiber 11 136 3 := by abel
      _ = _ := by rw [htwo, htwo, zero_add, zero_add]
  have hd := differential_add (differential_add h0 h3) h4
  rw [hsum] at hd
  refine ⟨x0+x3+x4, I.interpretation.basis .nuCofiber 11 136 3, ?_, ?_, ?_⟩
  · rw [hdecode 8 134 [0,3,4] (by decide), hx0', hx3', hx4']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      hdecode 11 136 [3] (by decide)
  · obtain ⟨hdeg, xr, yr, hxr, hyr, hd⟩ := hd
    refine ⟨hdeg, xr, yr, hxr, hyr, hd, ?_⟩
    obtain ⟨_, z, hz2, hz3⟩ := hyr
    have hB : ((E).ssData (11,136)).B 1 = ((E).ssData (11,136)).B 0 :=
      boundaries_succ_of_zero E 2 (by change (2 : ℤ) ≤ 2; omega) (9,135) (cnu_d2_zero I)
    rw [← hz3]
    exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hne)

end CnuDifferential

open CategoryTheory.Limits in
/-- The finite Cnu incoming exclusion used at the end of Proposition 7.9.
It uses complete degrees, not just the single level-9000 target row. -/
private theorem cnu_d2_d3_incoming14_zero (I : AdamsComputationTheorems D L G) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (11,137) = 0 ∧ ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) = 0 := by
  classical
  have hdecode (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber 11 137 indices = true) :
      I.interpretation.coordinateSum .nuCofiber 11 137 indices =
        some ((indices.map (I.interpretation.basis .nuCofiber 11 137)).sum) := by
    simp only [E2Interpretation.coordinateSum,hv,ite_true]
  have h0 : ∃ xr : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (11,137),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (I.interpretation.basis .nuCofiber 11 137 0) xr ∧
      ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) xr = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 76) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 11 137 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [0] (by decide)))
    subst y
    exact differential_target_cycle h
  have h3 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (I.interpretation.basis .nuCofiber 11 137 3) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 75) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 11 137 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [3] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h12 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 1000 (11,137)
      (I.interpretation.basis .nuCofiber 11 137 1 + I.interpretation.basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 77) (by rfl))
    have hx' : x = I.interpretation.basis .nuCofiber 11 137 1 + I.interpretation.basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [1,2] (by decide)))
    exact hx' ▸ h
  have h2 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 14 (11,137) (I.interpretation.basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 78) (by rfl))
    have hx' : x = I.interpretation.basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [2] (by decide)))
    exact hx' ▸ h
  obtain ⟨x12,hx12⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 1000) h12
  obtain ⟨x2,hx2⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 14) h2
  have hd12 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) x12 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx12 h12
  have hd2 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) x2 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx2 h2
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 44) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (11,137) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 11 137 i.val at he
  have hgen (i : Fin 4) : ∃ xr : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (11,137),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (e.symm (Finsupp.single i 1)) xr ∧ ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) xr = 0 := by
    rw [he]
    fin_cases i
    · exact h0
    · exact ⟨x12-x2, by simpa only [add_sub_cancel_right] using represents_sub hx12 hx2,
        by rw [map_sub,hd12,hd2,sub_self]⟩
    · exact ⟨x2,hx2,hd2⟩
    · exact ⟨0,h3,map_zero _⟩
  refine ⟨?_,d_zero_of_complete_representatives (by decide) e hgen⟩
  apply d_zero_of_complete_representatives (by decide) e
  intro i
  obtain ⟨xr,hxr,_⟩ := hgen i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
    (represents_two_self _) ⟨xr,hxr⟩


private theorem cnu_10_136_data (I : AdamsComputationTheorems D L G) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (10,136) = 0 ∧
    (∀ a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (10,136),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) ∨
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.interpretation.basis .nuCofiber 13 138 1) (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a)) ∧
    Subsingleton (((sequence D Raw.Spectrum.nuCofiber)).Page 4 (10,136)) := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.interpretation.coordinateSum .nuCofiber s t indices =
        some ((indices.map (I.interpretation.basis .nuCofiber s t)).sum) := by
    simp only [E2Interpretation.coordinateSum,hv,ite_true]
  obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 64) (by rfl))
  have hx' : x = I.interpretation.basis .nuCofiber 10 136 0 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hx.symm.trans (hdecode 10 136 [0] (by decide)))
  have hy' : y = I.interpretation.basis .nuCofiber 13 138 1 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hy.symm.trans (hdecode 13 138 [1] (by decide)))
  subst x y
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (13,138) _ _ at h
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h
  have hd' : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) xr = yr := by
    change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) xr = yr at hd
    exact hd
  have hne : yr ≠ 0 := by
    obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 51) (by rfl))
    change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 13 138 i.val at he
    have hn : I.interpretation.basis .nuCofiber 13 138 1 ≠ 0 := by
      rw [← he ⟨1,by decide⟩]
      intro hz
      have hh := congrArg e hz
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      change (Finsupp.single (⟨1,by decide⟩ : Fin 4) (1 : KIP126.Algebra.F2)) = 0 at hh
      exact Finsupp.single_ne_zero.mpr one_ne_zero hh
    obtain ⟨_,z,hz2,hz3⟩ := hyr
    have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 0 :=
      boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (11,137)
        (cnu_d2_d3_incoming14_zero I).1
    rw [← hz3]
    exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hn)
  have h1 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (I.interpretation.basis .nuCofiber 10 136 1) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 62) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 10 136 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [1] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h2 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (I.interpretation.basis .nuCofiber 10 136 2) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 63) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 10 136 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [2] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 39) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (10,136) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 10 136 i.val at he
  have hbas (i : Fin 3) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (e.symm (Finsupp.single i 1)) (![xr,0,0] i) := by
    rw [he]
    fin_cases i
    · exact hxr
    · exact h1
    · exact h2
  have hd2 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (10,136) = 0 := by
    apply d_zero_of_complete_representatives (by decide) e
    intro i
    refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
      (represents_two_self _) ⟨_,hbas i⟩
  have himage (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (10,136)) :
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) ∨
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.interpretation.basis .nuCofiber 13 138 1) (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) := by
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    by_cases hc0 : c 0 = 0
    · have ha : a = 0 := by simpa only [hc0,ite_true] using hc
      left
      have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = (0 : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138)) := by rw [ha,map_zero]
      exact hda.symm ▸ (RepresentsOnPage.zero (E := (sequence D Raw.Spectrum.nuCofiber)) (p := (13,138)) (by decide))
    · have ha : a = xr := by simpa only [hc0,ite_false] using hc
      right
      have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = yr := (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136)) ha).trans hd'
      exact hda.symm ▸ hyr
  have hzero (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 4 (10,136)) : a = 0 := by
    haveI : Epi ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 2) := by
      change Epi (cokernel.π _)
      infer_instance
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 2)).mp inferInstance a
    let x : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (10,136) := (Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).Z_anti
      (show (0 : WithTop ℕ) ≤ 2 by simp)) ≫ (((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 0) z
    have hx4 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (10,136) x a := ⟨by decide,z,rfl,hz⟩
    obtain ⟨ar,har⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 4) ⟨a,hx4⟩
    have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) ar = 0 := represents_d_zero_of_later
      (by change (2 : ℤ) ≤ 3; omega) (by decide) har ⟨a,hx4⟩
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas ar
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    have ha0 : ar = 0 := by
      by_cases hc0 : c 0 = 0
      · simpa only [hc0,ite_true] using hc
      · have ha : ar = xr := by simpa only [hc0,ite_false] using hc
        rw [ha,hd'] at hda
        exact False.elim (hne hda)
    exact represents_later_zero (by decide : (3 : ℤ) ≤ 4) (ha0 ▸ har) hx4
  exact ⟨hd2,himage,⟨fun a b => (hzero a).trans (hzero b).symm⟩⟩


private theorem cnu_page4_target3_nonzero (I : AdamsComputationTheorems D L G)
    (yr : ((sequence D Raw.Spectrum.nuCofiber)).Page 4 (13,138))
    (hy : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (13,138) (I.interpretation.basis .nuCofiber 13 138 3) yr) : yr ≠ 0 := by
  classical
  have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 0 :=
    boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (11,137)
      (cnu_d2_d3_incoming14_zero I).1
  have hback (x y : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138)) (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138))
      (hx : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) x a) (hy : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) y a) : x = y := by
    obtain ⟨_,z,hz2,hz3⟩ := hx
    obtain ⟨_,z',hz2',hz3'⟩ := hy
    exact hz2.symm.trans ((same_boundaries_projection_eq _ 0 1 (by simp) hB z z'
      (hz3.trans hz3'.symm)).trans hz2')
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 51) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 13 138 i.val at he
  have hn0 : I.interpretation.basis .nuCofiber 13 138 3 ≠ 0 := by
    rw [← he ⟨3,by decide⟩]
    intro hz
    have hh := congrArg e hz
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    change (Finsupp.single (⟨3,by decide⟩ : Fin 4) (1 : KIP126.Algebra.F2)) = 0 at hh
    exact Finsupp.single_ne_zero.mpr one_ne_zero hh
  have hn1 : I.interpretation.basis .nuCofiber 13 138 3 ≠ I.interpretation.basis .nuCofiber 13 138 1 := by
    rw [← he ⟨3,by decide⟩,← he ⟨1,by decide⟩]
    intro hz
    have hh := e.symm.injective hz
    have hval := congrArg (fun f : Fin 4 →₀ KIP126.Algebra.F2 => f ⟨3,by decide⟩) hh
    simp at hval
  intro hz
  obtain ⟨_,z,hz2,hz4⟩ := hy
  let ar : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138) := (Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z_anti
    (show (1 : WithTop ℕ) ≤ 2 by simp)) ≫ (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).pageπ 1) z
  have har : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.interpretation.basis .nuCofiber 13 138 3) ar := by
    refine ⟨by decide,Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z_anti
      (show (1 : WithTop ℕ) ≤ 2 by simp)) z,?_,rfl⟩
    change (Subobject.ofLE ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 1) ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 0) _ ≫
      (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).pageπ 0)
      ((Subobject.ofLE ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 2) ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 1) _) z) = _
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hh := (next_projection_zero_iff_incoming (sequence D Raw.Spectrum.nuCofiber) 3
    (by change (2 : ℤ) ≤ 3; omega) (10,136) z).mp (hz4.trans hz)
  obtain ⟨a,ha⟩ := hh
  change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = ar at ha
  rcases (cnu_10_136_data I).2.1 a with h0 | h1
  · have h0' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 ar := ha ▸ h0
    exact hn0 (hback _ _ _ har h0')
  · have h1' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.interpretation.basis .nuCofiber 13 138 1) ar := ha ▸ h1
    exact hn1 (hback _ _ _ har h1')


private theorem cnu_d5_incoming14_zero (I : AdamsComputationTheorems D L G) : ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) = 0 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.interpretation.coordinateSum .nuCofiber s t indices =
        some ((indices.map (I.interpretation.basis .nuCofiber s t)).sum) := by
    as_aux_lemma =>
      simp only [E2Interpretation.coordinateSum,hv,ite_true]
  obtain ⟨x0,hx0,y0,hy0,h0⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 51) (by rfl))
  have hx0' : x0 = I.interpretation.basis .nuCofiber 9 135 0 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx0.symm.trans (hdecode 9 135 [0] (by decide)))
  have hy0' : y0 = I.interpretation.basis .nuCofiber 12 137 4 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy0.symm.trans (hdecode 12 137 [4] (by decide)))
  subst x0 y0
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (12,137) _ _ at h0
  obtain ⟨_,xr0,yr0,hxr0,hyr0,hd0⟩ := h0
  change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) xr0 = yr0 at hd0
  have hn0 : yr0 ≠ 0 := by
    as_aux_lemma =>
      obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 47) (by rfl))
      change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
      change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 12 137 i.val at he
      have hn : I.interpretation.basis .nuCofiber 12 137 4 ≠ 0 := by
        as_aux_lemma =>
          rw [← he ⟨4,by decide⟩]
          intro hz
          have hh := congrArg e hz
          simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
          change (Finsupp.single (⟨4,by decide⟩ : Fin 5) (1 : KIP126.Algebra.F2)) = 0 at hh
          exact Finsupp.single_ne_zero.mpr one_ne_zero hh
      obtain ⟨_,z,hz2,hz3⟩ := hyr0
      have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (12,137)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (12,137)).B 0 :=
        boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (10,136) (cnu_10_136_data I).1
      rw [← hz3]
      exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hn)
  obtain ⟨x2,hx2,y2,hy2,h2⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 50) (by rfl))
  have hx2' : x2 = I.interpretation.basis .nuCofiber 9 135 2 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx2.symm.trans (hdecode 9 135 [2] (by decide)))
  have hy2' : y2 = I.interpretation.basis .nuCofiber 13 138 3 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy2.symm.trans (hdecode 13 138 [3] (by decide)))
  subst x2 y2
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 4 (9,135) (13,138) _ _ at h2
  obtain ⟨_,xr2,yr2,hxr2,hyr2,hd2⟩ := h2
  change ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) xr2 = yr2 at hd2
  have hn2 : yr2 ≠ 0 := cnu_page4_target3_nonzero I yr2 hyr2
  obtain ⟨x23,hx23⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 4) ⟨xr2,hxr2⟩
  have hd23 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) x23 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx23 ⟨xr2,hxr2⟩
  have h1 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 16 (9,135) (I.interpretation.basis .nuCofiber 9 135 1) := by
    as_aux_lemma =>
      obtain ⟨x,hx,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 49) (by rfl))
      have hx' : x = I.interpretation.basis .nuCofiber 9 135 1 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hx.symm.trans (hdecode 9 135 [1] (by decide)))
      exact hx' ▸ h
  obtain ⟨x13,hx13⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 16) h1
  obtain ⟨x14,hx14⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 16) h1
  obtain ⟨x15,hx15⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 5) (by decide : (5 : ℤ) ≤ 16) h1
  have hd13 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) x13 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx13 h1
  have hd14 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) x14 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 4; omega) (by decide) hx14 h1
  have hd15 : ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) x15 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 5; omega) (by decide) hx15 h1
  have h3 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (I.interpretation.basis .nuCofiber 9 135 3) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 47) (by rfl))
      have hy' : y = I.interpretation.basis .nuCofiber 9 135 3 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [3] (by decide)))
      subst y
      exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h4 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (I.interpretation.basis .nuCofiber 9 135 4) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 48) (by rfl))
      have hy' : y = I.interpretation.basis .nuCofiber 9 135 4 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [4] (by decide)))
      subst y
      exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 34) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 9 135 i.val at he
  have hbas (i : Fin 5) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (e.symm (Finsupp.single i 1)) (![xr0,x13,x23,0,0] i) := by
    as_aux_lemma =>
      rw [he]
      fin_cases i
      · exact hxr0
      · exact hx13
      · exact hx23
      · exact h3
      · exact h4
  ext a
  change ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) a = 0
  obtain ⟨x,hx5⟩ := page_has_initial_representative (by decide) a
  obtain ⟨ar3,har3⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 5) ⟨a,hx5⟩
  obtain ⟨ar4,har4⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 5) ⟨a,hx5⟩
  have hda3 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) ar3 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) har3 ⟨a,hx5⟩
  have hda4 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) ar4 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 4; omega) (by decide) har4 ⟨a,hx5⟩
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr0,x13,x23,0,0] hbas ar3
  have ha3 : ar3 = (if c 0=0 then 0 else xr0)+(if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
        Matrix.cons_val_succ,ite_self,← add_assoc] at hc
      exact hc
  have hb13 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) (if c 1=0 then 0 else x13) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd13
  have hb23 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) (if c 2=0 then 0 else x23) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd23
  have hc0 : c 0=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha3,map_add,map_add,hb13,hb23,add_zero,add_zero,if_neg hne,hd0] at hda3
      exact hn0 hda3
  have ha3' : ar3 = (if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simpa only [hc0,ite_true,zero_add] using ha3
  have hbit3 := represents_add (represents_bit (c 1) hx13) (represents_bit (c 2) hx23)
  have hbit3' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) _ ar3 := ha3'.symm ▸ hbit3
  have hbit4 := represents_add (represents_bit (c 1) hx14) (represents_bit (c 2) hxr2)
  have ha4 := represents_transport_eq (by decide : (3 : ℤ) ≤ 4) har3 hbit3' har4 hbit4
  have hb14 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) (if c 1=0 then 0 else x14) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd14
  have hc2 : c 2=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha4,map_add,hb14,zero_add,if_neg hne,hd2] at hda4
      exact hn2 hda4
  have ha4' : ar4 = (if c 1=0 then 0 else x14) := by simpa only [hc2,ite_true,add_zero] using ha4
  have hbit4' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (9,135) _ ar4 := ha4'.symm ▸ (represents_bit (c 1) hx14)
  have ha5 := represents_transport_eq (by decide : (4 : ℤ) ≤ 5) har4 hbit4' hx5 (represents_bit (c 1) hx15)
  rw [ha5]
  split_ifs
  · exact map_zero _
  · exact hd15


private theorem cnu_d2_incoming14_image (I : AdamsComputationTheorems D L G) (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138)) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) a = 0 ∨
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) a = I.interpretation.basis .nuCofiber 14 139 3 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.interpretation.coordinateSum .nuCofiber s t indices =
        some ((indices.map (I.interpretation.basis .nuCofiber s t)).sum) := by
    simp only [E2Interpretation.coordinateSum,hv,ite_true]
  have h0 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.interpretation.basis .nuCofiber 12 138 0) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 92) (by rfl))
    have hx' : x = I.interpretation.basis .nuCofiber 12 138 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [0] (by decide)))
    subst x
    obtain ⟨_,xr,_,hxr,_,_⟩ := h
    exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
      (represents_two_self _) ⟨xr,hxr⟩
  have h1 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.interpretation.basis .nuCofiber 12 138 1) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 90) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 12 138 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [1] (by decide)))
    subst y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    exact (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)) hyr.eq_on_page_two).trans hd
  have h3 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.interpretation.basis .nuCofiber 12 138 3) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 91) (by rfl))
    have hy' : y = I.interpretation.basis .nuCofiber 12 138 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [3] (by decide)))
    subst y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    exact (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)) hyr.eq_on_page_two).trans hd
  have h2 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.interpretation.basis .nuCofiber 12 138 2) =
      I.interpretation.basis .nuCofiber 14 139 3 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 93) (by rfl))
    have hx' : x = I.interpretation.basis .nuCofiber 12 138 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [2] (by decide)))
    have hy' : y = I.interpretation.basis .nuCofiber 14 139 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 14 139 [3] (by decide)))
    subst x y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (12,138) (14,139) _ _ at h
    exact differential_two_direct h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 48) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 12 138 i.val at he
  have hbas (i : Fin 4) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 2 (12,138) (e.symm (Finsupp.single i 1))
      (I.interpretation.basis .nuCofiber 12 138 i.val) := (he i) ▸ represents_two_self _
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e
    (fun i => I.interpretation.basis .nuCofiber 12 138 i.val) hbas a
  have ha : a = (if c 0=0 then 0 else I.interpretation.basis .nuCofiber 12 138 0)+
      (if c 1=0 then 0 else I.interpretation.basis .nuCofiber 12 138 1)+
      (if c 2=0 then 0 else I.interpretation.basis .nuCofiber 12 138 2)+
      (if c 3=0 then 0 else I.interpretation.basis .nuCofiber 12 138 3) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,← add_assoc] at hc
    exact hc
  let f : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138) →+ ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (14,139) := (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)).hom.toAddMonoidHom
  change f (I.interpretation.basis .nuCofiber 12 138 0) = 0 at h0
  change f (I.interpretation.basis .nuCofiber 12 138 1) = 0 at h1
  change f (I.interpretation.basis .nuCofiber 12 138 2) = I.interpretation.basis .nuCofiber 14 139 3 at h2
  change f (I.interpretation.basis .nuCofiber 12 138 3) = 0 at h3
  have hd : f a = if c 2=0 then 0 else I.interpretation.basis .nuCofiber 14 139 3 := by
    rw [ha,map_add,map_add,map_add]
    split_ifs <;> simp only [map_zero,h0,h1,h2,h3,zero_add,add_zero]

  change f a = 0 ∨ f a = I.interpretation.basis .nuCofiber 14 139 3
  by_cases hc2 : c 2=0
  · exact Or.inl (by simpa only [hc2,ite_true] using hd)
  · exact Or.inr (by simpa only [hc2,ite_false] using hd)


theorem cnu_target_through5 (I : AdamsComputationTheorems D L G) :
    Derived.CnuTargetThrough5 I.interpretation := by
  let S := sequence D Raw.Spectrum.nuCofiber

  -- Common representatives and actual boundary subobjects control passage between pages.
  -- Reconstruct all incoming maps from the complete degree-local bases.
  -- The nonzero d3 and d4 eliminate two source coordinates; the remaining class reaches page 16.
  -- At the final target, pages 3--5 add no boundaries, and the page-2 image is coordinate [3].
  have hdecode (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber 14 139 indices = true) :
      I.interpretation.coordinateSum .nuCofiber 14 139 indices =
        some ((indices.map (I.interpretation.basis .nuCofiber 14 139)).sum) := by
    as_aux_lemma =>
      simp only [E2Interpretation.coordinateSum,hv,ite_true]
  have hreach : ReachesPage S 1000 (14,139) (I.interpretation.basis .nuCofiber 14 139 2) := by
    as_aux_lemma =>
      obtain ⟨x,hx,h⟩ := I.adamsStatements _ (List.mem_of_getElem? (i := 110) (by rfl))
      have hx' : x = I.interpretation.basis .nuCofiber 14 139 2 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hx.symm.trans (hdecode [2] (by decide)))
      exact hx' ▸ h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 54) (by rfl))
  change (S).Page 2 (14,139) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .nuCofiber 14 139 i.val at he
  have hn0 : I.interpretation.basis .nuCofiber 14 139 2 ≠ 0 := by
    as_aux_lemma =>
      rw [← he ⟨2,by decide⟩]
      intro hz
      have hh := congrArg e hz
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      change (Finsupp.single (⟨2,by decide⟩ : Fin 4) (1 : KIP126.Algebra.F2)) = 0 at hh
      exact Finsupp.single_ne_zero.mpr one_ne_zero hh
  have hn3 : I.interpretation.basis .nuCofiber 14 139 2 ≠ I.interpretation.basis .nuCofiber 14 139 3 := by
    as_aux_lemma =>
      rw [← he ⟨2,by decide⟩,← he ⟨3,by decide⟩]
      intro hz
      have hh := e.symm.injective hz
      have hval := congrArg (fun f : Fin 4 →₀ KIP126.Algebra.F2 => f ⟨2,by decide⟩) hh
      simp at hval
  have hd4 : (S).d 4 (10,136) = 0 := by
    as_aux_lemma =>
      haveI := (cnu_10_136_data I).2.2
      ext x
      change (S).d 4 (10,136) x = 0
      rw [Subsingleton.elim x 0,map_zero]
  have hB2 : ((S).ssData (14,139)).B 2 = ((S).ssData (14,139)).B 1 :=
    boundaries_succ_of_zero S 3 (by change (2 : ℤ) ≤ 3; omega) (11,137) (cnu_d2_d3_incoming14_zero I).2
  have hB3 : ((S).ssData (14,139)).B 3 = ((S).ssData (14,139)).B 2 :=
    boundaries_succ_of_zero S 4 (by change (2 : ℤ) ≤ 4; omega) (10,136) hd4
  have hB4 : ((S).ssData (14,139)).B 4 = ((S).ssData (14,139)).B 3 :=
    boundaries_succ_of_zero S 5 (by change (2 : ℤ) ≤ 5; omega) (9,135) (cnu_d5_incoming14_zero I)
  have hB : ((S).ssData (14,139)).B 4 = ((S).ssData (14,139)).B 1 := hB4.trans (hB3.trans hB2)
  obtain ⟨yr,hyr⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 6) (by decide : (6 : ℤ) ≤ 1000) hreach
  have hne : yr ≠ 0 := by
    as_aux_lemma =>
      obtain ⟨_,z,hz2,hz6⟩ := hyr
      let z1 := (Subobject.ofLE (((S).ssData (14,139)).Z 4) (((S).ssData (14,139)).Z 1)
        (((S).ssData (14,139)).Z_anti (by simp))) z
      have hπ1 : ((S).ssData (14,139)).pageπ 1 z1 ≠ 0 := by
        as_aux_lemma =>
          intro hz1
          have hh := (next_projection_zero_iff_incoming S 2
            (by change (2 : ℤ) ≤ 2; omega) (12,138) z1).mp hz1
          obtain ⟨a,ha⟩ := hh
          have hπ2 : (Subobject.ofLE (((S).ssData (14,139)).Z 1) (((S).ssData (14,139)).Z 0)
              (((S).ssData (14,139)).Z_anti (by simp)) ≫
              ((S).ssData (14,139)).pageπ 0) z1 = I.interpretation.basis .nuCofiber 14 139 2 := by
            as_aux_lemma =>
              dsimp only [z1]
              rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
              exact hz2
          change (S).d 2 (12,138) a = (Subobject.ofLE (((S).ssData (14,139)).Z 1)
            (((S).ssData (14,139)).Z 0) _ ≫ ((S).ssData (14,139)).pageπ 0) z1 at ha
          rw [hπ2] at ha
          rcases cnu_d2_incoming14_image I a with hh | hh
          · exact hn0 (ha.symm.trans hh)
          · exact hn3 (ha.symm.trans hh)
      rw [← hz6]
      exact page_projection_nonzero _ 1 4 (by simp) hB z hπ1
  refine ⟨I.interpretation.basis .nuCofiber 14 139 2,?_,⟨yr,hyr,hne⟩,?_⟩
  · simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hdecode [2] (by decide)
  · refine ⟨by decide,by decide,?_⟩
    intro r hr hr5
    rintro ⟨q,hdeg,z,y,hy,hyne,hd⟩
    obtain ⟨x,hx⟩ := page_has_initial_representative hr z
    have hzero := differential_target_later_zero
      (by change (2 : ℤ) ≤ r; omega) (by omega : r < 6) ⟨hdeg,z,y,hx,hy,hd⟩
    exact hne (represents_unique hyr hzero)

/-- The distinguished sphere expressions agree with the fixed CSV expressions
under `I.interpretation`. Associativity identifies the two parenthesizations
of h₁h₄x₁₀₉,₁₂ in the target expression. -/
theorem distinguished_expression_comparisons (I : AdamsComputationTheorems D L G) :
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

/-- The high class used by the C tables and the high class used by the tmf
source have precisely the same product and factors, on this same M. -/
theorem high125_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 25 150 highClass = G.high125 M := by
  have h2 := I.products ⟨4, 24, 4, 24⟩ (by simp [Raw.products]) (atom .g) (atom .g)
  have h4 := I.products ⟨8, 48, 8, 48⟩ (by simp [Raw.products])
    (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g))
  have hHigh := I.products ⟨16, 96, 9, 54⟩ (by simp [Raw.products])
    (mulAt (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g)))
    (atom .delta_h_1_mul_g)
  dsimp only at h2 h4 hHigh
  change I.interpretation.sphere 25 150
    (mulAt (mulAt (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g)))
      (atom .delta_h_1_mul_g)) = _
  rw [hHigh, h4, h2, I.distinguishedClasses.g, I.distinguishedClasses.delta_h_1_mul_g]
  rfl

/-- The classical F26 vanishing needed to remove the indeterminacy of BMQ's
high125 detector.  Associated-graded convergence alone is insufficient:
Hausdorffness of this actual classical filtration is an explicit hypothesis.
It is a structural proof obligation, not an additional numerical A/C input. -/
theorem classical_stem125_filtration26_zero (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 125) : a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have hpage (s : ℕ) (hs : 26 ≤ s) :
        Subsingleton ((sequence D .sphere).Page 5 (s, (s : ℤ) + 125)) := by
      by_cases h64 : s ≤ 64
      · exact stem125_e5_zero_finite I s hs h64
      · exact sphere_page_zero_stem125_tail (D := D) V 5 s (by omega) (by omega)
    have hstep (s : ℕ) (hs : 26 ≤ s)
        (has : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum s 125) :
        a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum (s + 1) 125 := by
      let E := (sequence D .sphere).ssData (s, (s : ℤ) + 125)
      haveI : Subsingleton (E.page 3) := hpage s hs
      have hInf (z : E.eInfty) : z = 0 := by
        haveI : Epi (E.pageπ ⊤) := inferInstanceAs
          (Epi (CategoryTheory.Limits.cokernel.π _))
        obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance z
        have h := E.infinity_projection_eq_of_page_projection_eq 3 y 0
          (Subsingleton.elim _ _)
        change E.pageπ ⊤ y = 0
        simpa only [map_zero] using h
      have e : E.eInfty ≅
          (TowerDetection.filtration H.unit SphereSpectrum).associatedGraded s 125 := by
        dsimp only [E, sequence, object]
        simpa only [ClassicalObject.obj, add_sub_cancel_left] using
          (D.classicalConvergence .sphere).identification (s, (s : ℤ) + 125)
      have hmem : a ∈ (ModuleCat.subobjectModule _)
          ((TowerDetection.filtration H.unit SphereSpectrum).F s 125) := by
        simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using has
      obtain ⟨b, hb⟩ := hmem
      change ((TowerDetection.filtration H.unit SphereSpectrum).F s 125).arrow b = a at hb
      have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded
          s 125 b = 0 := by
        have h := congrArg e.hom (hInf
          (e.inv ((TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded s 125 b)))
        simpa only [← CategoryTheory.comp_apply, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, map_zero] using h
      have hnext := (subobject_cokernel_π_eq_zero_iff
        ((TowerDetection.filtration H.unit SphereSpectrum).F ((s : ℤ) + 1) 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).F s 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).mono s 125) b).mp hzero
      rw [hb] at hnext
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hnext
    apply S 125 a
    intro s
    by_cases hs : s ≤ 26
    · exact TowerDetection.filtrationSubmodule_antitone H.unit SphereSpectrum 125
        (by exact_mod_cast hs) ha
    · have h26 : 26 ≤ s := by omega
      clear hs
      induction s, h26 using Nat.le_induction with
      | base => exact ha
      | succ n hn ih =>
        simpa only [Nat.cast_add, Nat.cast_one] using hstep n hn ih

/-- Equality of two classical representatives follows only after proving
the higher-filtration indeterminacy zero.  The detection relation itself
remains associated-graded equality; it has not been replaced by strict equality. -/
theorem high125_detected_choice_unique (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a b : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.interpretation.sphere 25 150 highClass) a)
    (hb : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.interpretation.sphere 25 150 highClass) b) : a = b := by
  set_option backward.isDefEq.respectTransparency false in
    dsimp only [TowerDetection.Detects, ClassicalObject.obj] at ha hb
    obtain ⟨z, hz, a', ha', hga⟩ := ha
    obtain ⟨z', hz', b', hb', hgb⟩ := hb
    have heq := ((sequence D .sphere).ssData (25, 150)).infinity_projection_eq_of_page_projection_eq 0 z z' (hz.trans hz'.symm)
    have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded 25 (150 - 25) (a' - b') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (hga.symm.trans
        ((congrArg ((D.classicalConvergence .sphere).identification (25, 150)).hom heq).trans hgb))
    have hmem := (subobject_cokernel_π_eq_zero_iff
      ((TowerDetection.filtration H.unit SphereSpectrum).F 26 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).F 25 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).mono 25 (150 - 25))
      (a' - b')).mp hzero
    rw [map_sub, ha', hb'] at hmem
    have hab : a - b ∈
        TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 (150 - 25) := by
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hmem
    exact sub_eq_zero.mp (classical_stem125_filtration26_zero I V S (a - b) hab)


end
end KIP126.Computation.SphereAndCofiber
end
