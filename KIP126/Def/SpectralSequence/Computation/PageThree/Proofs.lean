module

public import KIP126.Def.SpectralSequence.Computation.State.Proofs
public import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs

@[expose] public section


/-! Third-page representatives for the existing module-valued internal
spectral sequence. All pages and representatives use the original SSData
quotients. No computation output, coordinate comparison, or coverage premise
enters these generic statements. -/
namespace KIP126.Core.SpectralSequence.PageThree

open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
variable {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}

/-- Every actual E₃ element has an E₂ label with the same common cycle
representative. No nonvanishing or basis assumption is required. -/
theorem exists_representative (p : ℤ × ℤ) (y : E.Page 3 p) :
    ∃ x : E.Page 2 p, RepresentsOnPage E 3 p x y := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(3 - E.r₀).toNat
  let a := Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti (by
    dsimp only [n, m]
    exact_mod_cast (show (2 - E.r₀).toNat ≤ (3 - E.r₀).toNat by omega))) ≫ D.pageπ n
  letI : Epi (D.pageπ m) := coequalizer.π_epi
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ m)).mp inferInstance y
  exact ⟨a z, by decide, z, rfl, hz⟩

/-- A full E₂ label admits an E₃ representative exactly when its actual d₂
is zero. This ranges over every degree and every label. -/
theorem reachesPage_iff_d2_eq_zero (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (x : E.Page 2 p) : ReachesPage E 3 p x ↔ E.d 2 p x = 0 := by
  have hm : (3 - E.r₀).toNat = (2 - E.r₀).toNat + 1 := by omega
  have hk := congrArg (ModuleCat.subobjectModule (E.Page 2 p)) (E.Z_succ 2 p hstart)
  rw [subobjectModule_kernel, subobjectModule_image] at hk
  have hindexed (m : ℕ) (hnm : (2 - E.r₀).toNat ≤ m)
      (heq : m = (2 - E.r₀).toNat + 1) :
      LinearMap.ker (E.d 2 p).hom = LinearMap.range
        (Subobject.ofLE ((E.ssData p).Z ↑m) ((E.ssData p).Z ↑(2 - E.r₀).toNat)
          ((E.ssData p).Z_anti (by exact_mod_cast hnm)) ≫
          (E.ssData p).pageπ ↑(2 - E.r₀).toNat).hom := by
    subst m
    exact hk
  have hk := hindexed (3 - E.r₀).toNat (by omega) hm
  constructor
  · rintro ⟨y, _, z, hx, _⟩
    have hmem : x ∈ LinearMap.ker (E.d 2 p).hom := by
      rw [hk]
      exact ⟨z, hx⟩
    exact hmem
  · intro hx
    have hmem : x ∈ LinearMap.ker (E.d 2 p).hom := hx
    rw [hk] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨(E.ssData p).pageπ ↑(3 - E.r₀).toNat z, by decide, z, hz, rfl⟩

private theorem represents_sub {r : ℤ} {p : ℤ × ℤ}
    {a b : E.Page 2 p} {x y : E.Page r p}
    (ha : RepresentsOnPage E r p a x) (hb : RepresentsOnPage E r p b y) :
    RepresentsOnPage E r p (a - b) (x - y) := by
  obtain ⟨hr, z, hza, hzx⟩ := ha
  obtain ⟨_, w, hwb, hwy⟩ := hb
  exact ⟨hr, z - w, by simp only [map_sub, hza, hwb],
    by simp only [map_sub, hzx, hwy]⟩

/-- Cumulative second-page boundaries have the zero third-page representative. -/
private theorem boundary_represents_zero {p : ℤ × ℤ} {x : E.Page 2 p}
    (h : IsBoundaryBy E 2 p x) : RepresentsOnPage E 3 p x 0 := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(2 + 1 - E.r₀).toNat
  obtain ⟨_, b, hb⟩ := h
  refine ⟨by decide, Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) b, ?_, ?_⟩
  · change (Subobject.ofLE (D.B m) (D.Z m) (D.B_le_Z m) ≫
        Subobject.ofLE (D.Z m) (D.Z n) _ ≫ D.pageπ n) b = x
    simpa only [D, m, n, ← Category.assoc, Subobject.ofLE_comp_ofLE] using hb
  · exact cokernel.condition_apply _ b

/-- The cumulative boundary condition after d₂ is precisely the image of
that actual d₂. Indexing the target by `p + diffDeg 2` avoids choosing any
unrelated grading transport; as p varies this covers every target degree. -/
theorem isBoundaryBy_iff_mem_d2_range (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (x : E.Page 2 (p + E.diffDeg 2)) :
    IsBoundaryBy E 2 (p + E.diffDeg 2) x ↔ x ∈ LinearMap.range (E.d 2 p).hom := by
  have hm : (2 + 1 - E.r₀).toNat = (2 - E.r₀).toNat + 1 := by omega
  have hb := congrArg (ModuleCat.subobjectModule (E.Page 2 (p + E.diffDeg 2)))
    (E.B_succ 2 p hstart)
  rw [subobjectModule_image, subobjectModule_image] at hb
  have hindexed (m : ℕ) (hnm : (2 - E.r₀).toNat ≤ m)
      (heq : m = (2 - E.r₀).toNat + 1) :
      LinearMap.range (E.d 2 p).hom = LinearMap.range
        (Subobject.ofLE ((E.ssData (p + E.diffDeg 2)).B ↑m)
          ((E.ssData (p + E.diffDeg 2)).Z ↑(2 - E.r₀).toNat)
          (((E.ssData (p + E.diffDeg 2)).B_le_Z ↑m).trans
            ((E.ssData (p + E.diffDeg 2)).Z_anti (by exact_mod_cast hnm))) ≫
          (E.ssData (p + E.diffDeg 2)).pageπ ↑(2 - E.r₀).toNat).hom := by
    subst m
    exact hb
  have hb := hindexed (2 + 1 - E.r₀).toNat (by omega) hm
  constructor
  · rintro ⟨_, b, hx⟩
    rw [hb]
    refine ⟨b, ?_⟩
    simpa only [← Category.assoc, Subobject.ofLE_comp_ofLE] using hx
  · intro hx
    rw [hb] at hx
    obtain ⟨b, hx⟩ := hx
    exact ⟨by decide, b, by
      simpa only [← Category.assoc, Subobject.ofLE_comp_ofLE] using hx⟩

private theorem represents_add {r : ℤ} {p : ℤ × ℤ}
    {a b : E.Page 2 p} {x y : E.Page r p}
    (ha : RepresentsOnPage E r p a x) (hb : RepresentsOnPage E r p b y) :
    RepresentsOnPage E r p (a + b) (x + y) := by
  obtain ⟨hr, z, hza, hzx⟩ := ha
  obtain ⟨_, w, hwb, hwy⟩ := hb
  exact ⟨hr, z + w, by simp only [map_add, hza, hwb],
    by simp only [map_add, hzx, hwy]⟩

/-- Two E₂ labels represent the same specified E₃ element exactly when
their difference is an incoming actual d₂ boundary. Only one label is
assumed to represent that element; the converse constructs the other. -/
theorem represents_iff_sub_mem_d2_range (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    {a b : E.Page 2 (p + E.diffDeg 2)} {y : E.Page 3 (p + E.diffDeg 2)}
    (ha : RepresentsOnPage E 3 (p + E.diffDeg 2) a y) :
    RepresentsOnPage E 3 (p + E.diffDeg 2) b y ↔
      b - a ∈ LinearMap.range (E.d 2 p).hom := by
  constructor
  · intro hb
    apply (isBoundaryBy_iff_mem_d2_range hstart p (b - a)).mp
    exact (RepresentsOnPage.eq_zero_iff_isBoundaryBy (r := 2) (by decide)
      (represents_sub hb ha)).mp (sub_self y)
  · intro hba
    have hzero := boundary_represents_zero
      ((isBoundaryBy_iff_mem_d2_range hstart p (b - a)).mpr hba)
    simpa only [sub_add_cancel, zero_add] using represents_add hzero ha

/-- Equality of the actual third-page classes is detected by the complete
incoming d₂ image, without a finite-coordinate restriction. -/
theorem equal_iff_sub_mem_d2_range (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    {a b : E.Page 2 (p + E.diffDeg 2)} {x y : E.Page 3 (p + E.diffDeg 2)}
    (ha : RepresentsOnPage E 3 (p + E.diffDeg 2) a x)
    (hb : RepresentsOnPage E 3 (p + E.diffDeg 2) b y) :
    x = y ↔ a - b ∈ LinearMap.range (E.d 2 p).hom := by
  calc
    x = y ↔ IsBoundaryBy E 2 (p + E.diffDeg 2) (a - b) := by
      have h : x - y = 0 ↔ IsBoundaryBy E 2 (p + E.diffDeg 2) (a - b) :=
        RepresentsOnPage.eq_zero_iff_isBoundaryBy (r := 2) (by decide)
          (represents_sub ha hb)
      exact (sub_eq_zero (a := x) (b := y)).symm.trans h
    _ ↔ a - b ∈ LinearMap.range (E.d 2 p).hom :=
      isBoundaryBy_iff_mem_d2_range hstart p (a - b)

end KIP126.Core.SpectralSequence.PageThree
