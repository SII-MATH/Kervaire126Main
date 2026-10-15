module

public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.SpectralSequence.Computation.CyclesAndBoundaries.Predicates
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs

@[expose] public section

/-! Third-page representatives for the existing module-valued internal
spectral sequence. All pages and representatives use the original SSData
quotients. No computation output, coordinate comparison, or coverage premise
enters these generic statements. -/
namespace KIP126.SpectralSequence.PageThree

open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]
variable {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}

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

end KIP126.SpectralSequence.PageThree
