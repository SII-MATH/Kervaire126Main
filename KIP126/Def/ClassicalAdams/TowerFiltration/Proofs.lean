module

public import KIP126.Def.ClassicalAdams.TowerFiltration.Data
public import KIP126.Def.ClassicalAdams.TowerPages.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Liftability through more tower stages implies liftability through fewer. -/
theorem adamsCycles_le_of_le (s t : ℤ) (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hrq : r ≤ q) : adamsCycles unit X q hq s t ≤ adamsCycles unit X r hr s t := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨adamsI unit X (t - s - 1) (s + r) (s + q) (by omega) y, ?_⟩
  rw [adamsI_comp]
  exact hy

theorem adamsFiniteCycleSubmodule_antitone (s t : ℤ) :
    Antitone (adamsFiniteCycleSubmodule unit X s t) := by
  intro i j hij x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨adamsI unit X (t - s - 1) (s + (i + 2 : ℕ))
    (s + (j + 2 : ℕ)) (by omega) y, ?_⟩
  rw [adamsI_comp]
  exact hy

theorem adamsFiniteBoundarySubmodule_monotone (s t : ℤ) :
    Monotone (adamsFiniteBoundarySubmodule unit X s t) := by
  intro i j hij x hx
  obtain ⟨y, hy, hj⟩ := hx
  refine ⟨y, ?_, hj⟩
  change adamsI unit X (t - s) (s - (i + 2 : ℕ) + 1) s (by omega) y = 0 at hy
  change adamsI unit X (t - s) (s - (j + 2 : ℕ) + 1) s (by omega) y = 0
  rw [← adamsI_comp unit X (t - s) (s - (j + 2 : ℕ) + 1)
    (s - (i + 2 : ℕ) + 1) s (by omega) (by omega), hy, map_zero]

/-- A boundary at any stage is a cycle at every stage, by exactness `kj = 0`. -/
theorem adamsFiniteBoundarySubmodule_le_cycle (s t : ℤ) (i j : ℕ) :
    adamsFiniteBoundarySubmodule unit X s t i ≤
      adamsFiniteCycleSubmodule unit X s t j := by
  intro x hx
  obtain ⟨y, _, hj⟩ := hx
  change adamsJ unit X s t y = x.val at hj
  change x.val ∈ adamsCycles unit X (j + 2) (by omega) s t
  rw [← hj]
  exact adamsJ_mem_cycles unit X (j + 2) (by omega) s t y

@[simp] theorem adamsFiniteCycleSubmodule_zero (s t : ℤ) :
    adamsFiniteCycleSubmodule unit X s t 0 = ⊤ := by
  exact Submodule.comap_subtype_self _

theorem adamsCycleSubmodule_antitone (s t : ℤ) :
    Antitone (adamsCycleSubmodule unit X s t) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top =>
      change (⨅ n : ℕ, adamsFiniteCycleSubmodule unit X s t n) ≤ _
      exact iInf_le _ i
    | coe j =>
      exact adamsFiniteCycleSubmodule_antitone unit X s t
        (WithTop.coe_le_coe.mp hij)

theorem adamsBoundarySubmodule_monotone (s t : ℤ) :
    Monotone (adamsBoundarySubmodule unit X s t) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top =>
      change _ ≤ ⨆ n : ℕ, adamsFiniteBoundarySubmodule unit X s t n
      exact le_iSup (adamsFiniteBoundarySubmodule unit X s t) i
    | coe j =>
      exact adamsFiniteBoundarySubmodule_monotone unit X s t
        (WithTop.coe_le_coe.mp hij)

theorem adamsBoundarySubmodule_le_cycle (s t : ℤ) (r : WithTop ℕ) :
    adamsBoundarySubmodule unit X s t r ≤ adamsCycleSubmodule unit X s t r := by
  cases r using WithTop.recTopCoe with
  | top => exact iSup_le fun i => le_iInf fun j =>
      adamsFiniteBoundarySubmodule_le_cycle unit X s t i j
  | coe n => exact adamsFiniteBoundarySubmodule_le_cycle unit X s t n n

/-- Membership at infinity means membership in every finite tower cycle module. -/
theorem mem_adamsCycleSubmodule_top (s t : ℤ) (x : adamsCycleAmbient unit X s t) :
    x ∈ adamsCycleSubmodule unit X s t ⊤ ↔
      ∀ n : ℕ, x.val ∈ adamsCycles unit X (n + 2) (by omega) s t := by
  simp only [adamsCycleSubmodule, Submodule.mem_iInf]
  rfl

/-- An infinite-stage boundary already occurs at some finite stage. -/
theorem mem_adamsBoundarySubmodule_top (s t : ℤ) (x : adamsCycleAmbient unit X s t) :
    x ∈ adamsBoundarySubmodule unit X s t ⊤ ↔
      ∃ n : ℕ, x.val ∈ adamsBoundaries unit X (n + 2) (by omega) s t := by
  exact Submodule.mem_iSup_of_directed (adamsFiniteBoundarySubmodule unit X s t)
    (adamsFiniteBoundarySubmodule_monotone unit X s t).directed_le

end
end KIP126.Classical.Adams
