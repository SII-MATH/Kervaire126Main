module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Boundary.Proofs

@[expose] public section

/-! Exact quotient criteria and the existing h₆² detector on cobar cohomology. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

@[simp] theorem mem_boundariesInCycles {s t : ℕ} (x : cycles s t) :
    x ∈ boundariesInCycles H M s t ↔ x.val ∈ boundaries s t := by
  rw [boundariesInCycles, Submodule.range_inclusion]
  rfl

/-- The quotient kills precisely the incoming cobar boundaries. -/
theorem classOf_eq_zero_iff {s t : ℕ} (x : cycles s t) :
    classOf H M s t x = 0 ↔ x.val ∈ boundaries s t :=
  (Submodule.Quotient.mk_eq_zero _).trans (mem_boundariesInCycles H M x)

/-- Two specified cycles represent the same class exactly when their
actual cochains differ by an incoming cobar boundary. -/
theorem classOf_eq_iff {s t : ℕ} (x y : cycles s t) :
    classOf H M s t x = classOf H M s t y ↔
      x.val - y.val ∈ boundaries s t :=
  (Submodule.Quotient.eq _).trans (mem_boundariesInCycles H M (x - y))

theorem ofCocycle_eq_zero_iff {s t : ℕ} (x : cochains s t)
    (hx : differential s t x = 0) :
    ofCocycle H M x hx = 0 ↔ x ∈ boundaries s t :=
  classOf_eq_zero_iff H M ⟨x, hx⟩

/-- At zero there is no quotient by an artificial `d₋₁` or by `d₀`. -/
theorem ofCocycle_zero_eq_zero_iff (t : ℕ) (x : cochains 0 t)
    (hx : differential 0 t x = 0) :
    ofCocycle H M x hx = 0 ↔ x = 0 := by
  simpa only [boundaries_zero, Submodule.mem_bot] using ofCocycle_eq_zero_iff H M x hx

/-- In positive cohomological degree, zero means an actual preceding cochain
whose differential is the specified representative. -/
theorem ofCocycle_succ_eq_zero_iff (s t : ℕ) (x : cochains (s + 1) t)
    (hx : differential (s + 1) t x = 0) :
    ofCocycle H M x hx = 0 ↔ ∃ y : cochains s t, differential s t y = x :=
  ofCocycle_eq_zero_iff H M x hx

/-- Every differential represents zero; closedness is supplied by the
already proved square-zero law for this same comparison. -/
theorem classOf_differential (s t : ℕ) (x : cochains s t) :
    ofCocycle H M (differential s t x) (milnor_differential_squared H M s t x) = 0 :=
  (ofCocycle_succ_eq_zero_iff H M s t _ _).mpr ⟨x, rfl⟩

/-- Exact boundary criterion for the specified standard generator. -/
theorem hi_eq_zero_iff (i : ℕ) :
    hi H M i = 0 ↔
      ∃ b : cochains 0 (2 ^ i), differential 0 (2 ^ i) b = hiCochain i :=
  ofCocycle_succ_eq_zero_iff H M 0 (2 ^ i) _ _

/-- Exact boundary criterion for the specified concatenation square. -/
theorem hiSquare_eq_zero_iff (i : ℕ) :
    hiSquare H M i = 0 ↔ ∃ b : cochains 1 (2 ^ (i + 1)),
      differential 1 (2 ^ (i + 1)) b = hiSquareCochain i :=
  ofCocycle_succ_eq_zero_iff H M 1 (2 ^ (i + 1)) _ _

/-- The existing polynomial detector proves that this particular class is
nonzero in the actual cohomology quotient. No blanket nonvanishing for all
`hiSquare` classes is assumed. -/
theorem hiSquare_six_ne_zero : hiSquare H M 6 ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := (hiSquare_eq_zero_iff H M 6).mp h
  exact h6SquareCochain_not_boundary b hb

end
end KIP126.Classical.Adams.MilnorCohomology
