module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
public import KIP126.Def.SpectralSequence.Computation.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open CategoryTheory CategoryTheory.Limits
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
  KIP126.SpectralSequence

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The first paper cycle submodule is all of E₂, after taking the quotient. -/
@[simp] theorem cycles_one (p : ℤ × ℤ) : cycles H X 1 p = ⊤ := by
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  letI : Epi (D.pageπ 0) := by
    exact coequalizer.π_epi
  change LinearMap.range (cycleMap H X 0 p).hom = ⊤
  simp only [cycleMap, Subobject.ofLE_refl, Category.id_comp]
  exact LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective (D.pageπ 0)).mp inferInstance)

/-- The initial raw boundaries vanish in E₂. -/
@[simp] theorem boundaries_one (p : ℤ × ℤ) : boundaries H X 1 p = ⊥ := by
  change LinearMap.range (boundaryMap H X 0 p).hom = ⊥
  have h : boundaryMap H X 0 p = 0 := by
    exact cokernel.condition _
  rw [h]
  exact LinearMap.range_zero

/-- Paper Z_{r−1} means that a common representative exists on actual page r.
This allows classes whose continuation is zero. -/
theorem isCycle_iff_represents (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (x : Ambient H X p) :
    IsCycle H X (r - 1) p x ↔
      ∃ xr : (adamsTowerInternalSpectralSequence H.unit X).Page r p,
        RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x xr := by
  have hn : r - 1 - 1 = r - 2 := by omega
  constructor
  · rintro ⟨_, hx⟩
    change ∃ z, (cycleMap H X (↑(r - 1 - 1).toNat) p).hom z = x at hx
    rw [hn] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨_, hr, z, ?_, rfl⟩
    exact hz
  · rintro ⟨xr, _, z, hx, _⟩
    refine ⟨by omega, ?_⟩
    change ∃ z, (cycleMap H X (↑(r - 1 - 1).toNat) p).hom z = x
    rw [hn]
    exact ⟨z, hx⟩

/-- The source and target of a displayed differential have actual page-r representatives. -/
theorem DifferentialAt.cycles {r : ℤ} {p q : ℤ × ℤ}
    {x : Ambient H X p} {y : Ambient H X q}
    (h : DifferentialAt H X r p q x y) :
    IsCycle H X (r - 1) p x ∧ IsCycle H X (r - 1) q y := by
  obtain ⟨hr, _, xr, yr, hx, hy, _⟩ := h
  exact ⟨(isCycle_iff_represents H X r hr p x).mpr ⟨xr, hx⟩,
    (isCycle_iff_represents H X r hr q y).mpr ⟨yr, hy⟩⟩

end
end KIP126.Classical.Adams.PageRepresentatives
