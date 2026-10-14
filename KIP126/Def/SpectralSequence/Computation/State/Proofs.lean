module

public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.SpectralSequence.Computation.State.Predicates
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section


/-!
# Actual page representatives and cumulative boundaries

These rules refer only to the internal nested-subobject spectral sequence.
They do not assume that a program-maintained boundary span agrees with these
actual boundary subobjects; that comparison must be certified separately.
-/

namespace KIP126.Core.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]

/-- An actual quotient-page element is zero exactly when its cycle representative
comes from the actual boundary subobject. -/
theorem SSData.pageπ_eq_zero_iff (D : SSData (ModuleCat.{v} R)) (n : WithTop ℕ)
    (z : (Subobject.underlying.obj (D.Z n) : ModuleCat R)) :
    D.pageπ n z = 0 ↔ ∃ b : (Subobject.underlying.obj (D.B n) : ModuleCat R),
      Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n) b = z := by
  let i := Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n)
  have h := ShortComplex.cokernelSequence_exact i
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp h z
  · rintro ⟨b, rfl⟩
    exact cokernel.condition_apply i b

/-- Existence of a continuation and vanishing on every continuation give a
differential equation with the zero label. -/
theorem ReachesPage.hasDifferential_zero
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p q : ℤ × ℤ}
    {x : E.Page 2 p} (hr : 2 ≤ r) (hdeg : p + E.diffDeg r = q)
    (hx : ReachesPage E r p x) (hz : DifferentialVanishesOn E r p x) :
    HasDifferential E r p q x 0 := by
  obtain ⟨xr, hxr⟩ := hx
  refine ⟨hdeg, xr, 0, hxr, RepresentsOnPage.zero hr, ?_⟩
  simp only [ModuleCat.comp_apply, hz xr hxr, map_zero]

/-- Two later-cycle representatives equal on an earlier page remain equal on
the later page: the earlier boundaries are included in the later boundaries. -/
theorem SSData.page_eq_of_early_page_eq (D : SSData (ModuleCat.{v} R))
    (n m : WithTop ℕ) (hnm : n ≤ m)
    (z w : (Subobject.underlying.obj (D.Z m) : ModuleCat R))
    (h : (Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm) ≫ D.pageπ n) z =
      (Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm) ≫ D.pageπ n) w) :
    D.pageπ m z = D.pageπ m w := by
  let a := Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm)
  have hz : D.pageπ n (a (z - w)) = 0 := by
    change (a ≫ D.pageπ n) (z - w) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨b, hb⟩ := (D.pageπ_eq_zero_iff n (a (z - w))).mp hz
  let bm := Subobject.ofLE (D.B n) (D.B m) (D.B_mono hnm) b
  have hm : Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) bm = z - w := by
    apply (ModuleCat.mono_iff_injective a).mp inferInstance
    change (Subobject.ofLE (D.B n) (D.B m) (D.B_mono hnm) ≫
      Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) ≫ a) b = a (z - w)
    simpa only [a, Subobject.ofLE_comp_ofLE] using hb
  have hm0 := (D.pageπ_eq_zero_iff m (z - w)).mpr ⟨bm, hm⟩
  simpa only [map_sub, sub_eq_zero] using hm0

/-- A fixed E₂ label has at most one actual continuation on any later page.
This does not assert that a continuation exists. -/
theorem RepresentsOnPage.unique
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {yr zr : E.Page r p}
    (hy : RepresentsOnPage E r p x yr) (hz : RepresentsOnPage E r p x zr) :
    yr = zr := by
  obtain ⟨hr, y, hxy, hy⟩ := hy
  obtain ⟨_, z, hxz, hz⟩ := hz
  have hnm : (↑(2 - E.r₀).toNat : WithTop ℕ) ≤ ↑(r - E.r₀).toNat := by
    exact_mod_cast (show (2 - E.r₀).toNat ≤ (r - E.r₀).toNat by omega)
  exact hy.symm.trans (((E.ssData p).page_eq_of_early_page_eq _ _ hnm y z
    (hxy.trans hxz.symm)).trans hz)

/-- A represented class on page `r + 1` is zero exactly when its E₂ label is
in the actual cumulative boundary subobject after page `r`. -/
theorem RepresentsOnPage.eq_zero_iff_isBoundaryBy
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {yr : E.Page (r + 1) p} (hr : 2 ≤ r)
    (hrep : RepresentsOnPage E (r + 1) p x yr) :
    yr = 0 ↔ IsBoundaryBy E r p x := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp [n, m]
    exact_mod_cast (show (2 - E.r₀).toNat ≤ (r + 1 - E.r₀).toNat by omega)
  constructor
  · intro hy0
    obtain ⟨_, z, hx, hy⟩ := hrep
    have hz : D.pageπ m z = 0 := hy.trans hy0
    obtain ⟨b, hb⟩ := (D.pageπ_eq_zero_iff m z).mp hz
    refine ⟨hr, b, ?_⟩
    rw [← hb] at hx
    change (Subobject.ofLE (D.B m) (D.B ⊤) (D.B_mono le_top) ≫
      Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
      Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) b = x
    change (Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) ≫
      Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm) ≫ D.pageπ n) b = x at hx
    simpa only [← Category.assoc, Subobject.ofLE_comp_ofLE] using hx
  · rintro ⟨_, b, hb⟩
    have hrep0 : RepresentsOnPage E (r + 1) p x 0 := by
      refine ⟨by omega,
        Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) b, ?_, ?_⟩
      · change (Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) ≫
          Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hnm) ≫ D.pageπ n) b = x
        simpa only [D, m, n, ← Category.assoc, Subobject.ofLE_comp_ofLE] using hb
      · exact cokernel.condition_apply _ b
    exact hrep.unique hrep0

/-- A differential equation with the zero E₂ source label can only target an
E₂ label already in the cumulative boundary space before that differential.
The page bound is exactly the range in which `IsBoundaryBy (r - 1)` is defined.
This uses actual common representatives, not a program boundary-span test. -/
theorem HasDifferential.isBoundaryBy_of_source_zero
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p q : ℤ × ℤ}
    {y : E.Page 2 q} (hr : 3 ≤ r) (h : HasDifferential E r p q 0 y) :
    IsBoundaryBy E (r - 1) q y := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  have hx0 : xr = 0 := hx.unique (RepresentsOnPage.zero (by omega))
  have hy0 : yr = 0 := by
    simpa only [hx0, ModuleCat.comp_apply, map_zero] using hd.symm
  simpa only [add_sub_cancel_right] using
    (hy.eq_zero_iff_isBoundaryBy (by omega)).mp hy0

/-- An actual earlier-boundary exclusion refutes a zero-source equation.
A database diagnostic asserting this exclusion is not a proof of the premise. -/
theorem not_hasDifferential_zero_of_not_isBoundaryBy
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p q : ℤ × ℤ}
    {y : E.Page 2 q} (hr : 3 ≤ r) (hy : ¬ IsBoundaryBy E (r - 1) q y) :
    ¬ HasDifferential E r p q 0 y :=
  fun h => hy (h.isBoundaryBy_of_source_zero hr)

/-- A label excluded from the actual cumulative boundary space has a nonzero
next-page continuation whenever a continuation exists. -/
theorem ReachesPage.survives_of_not_isBoundaryBy
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} (hr : 2 ≤ r) (hx : ReachesPage E (r + 1) p x)
    (hboundary : ¬ IsBoundaryBy E r p x) : SurvivesTo E (r + 1) p x := by
  obtain ⟨xr, hxr⟩ := hx
  exact ⟨xr, hxr, fun hz => hboundary ((hxr.eq_zero_iff_isBoundaryBy hr).mp hz)⟩

/-- Actual target exhaustiveness and exclusion of its nonzero alternative
prove the zero differential once the source has an actual continuation. -/
theorem hasDifferential_zero_of_excluded_target
    {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} (hr : 2 ≤ r) (hx : ReachesPage E r p x)
    (y : E.Page 2 (p + E.diffDeg r))
    (htargets : DifferentialTargets E r p x y)
    (hexclude : ¬ HasNonzeroDifferential E r p (p + E.diffDeg r) x y) :
    HasDifferential E r p (p + E.diffDeg r) x 0 := by
  exact hx.hasDifferential_zero hr rfl
    ((differentialVanishesOn_iff_not_hasNonzeroDifferential y htargets).mpr hexclude)

end KIP126.Core.SpectralSequence
