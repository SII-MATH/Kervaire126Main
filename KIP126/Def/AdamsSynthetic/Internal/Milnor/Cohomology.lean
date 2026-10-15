module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.Def.AdamsSynthetic.Internal.Milnor.Complex
import all KIP126.Def.AdamsSynthetic.Internal.Milnor.Hi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.BilinearMap

@[expose] section

/-! Actual normalized Milnor cobar cohomology and descended concatenation.
Adapted from SII-MATH/Kervaire126 (MIT), develop commit
8cb35dad5f75ecc095e474df6c765baec9b175bf, ClassicalAdams/MilnorCohomology.
The sole square-zero input is the independently stated property of the fixed
polynomial differential. No Adams tower or cooperation comparison is used.
The cup product is constructed by quotient descent, not chosen as data. -/

namespace KIP126.AdamsSynthetic.Milnor

/- Adapted from MilnorCohomology/Complex/Data.lean. -/
noncomputable section

/-- The kernel of the explicit coproduct differential in bidegree `(s,t)`. -/
def cycles (s t : ℕ) : Submodule F2 (cochains s t) :=
  LinearMap.ker (differential s t)

/-- The incoming image, with no incoming cochains in homological degree zero.
In degree `s+1` this is exactly `range (differential s t)`. -/
def boundaries : (s t : ℕ) → Submodule F2 (cochains s t)
  | 0, _ => ⊥
  | s + 1, t => LinearMap.range (differential s t)

end

/- Adapted from MilnorCohomology/Complex/Proofs.lean. -/
noncomputable section


@[simp] theorem mem_cycles (s t : ℕ) (x : cochains s t) :
    x ∈ cycles s t ↔ differential s t x = 0 := Iff.rfl

@[simp] theorem boundaries_zero (t : ℕ) : boundaries 0 t = ⊥ := rfl

@[simp] theorem boundaries_succ (s t : ℕ) :
    boundaries (s + 1) t = LinearMap.range (differential s t) := rfl

/-- The independently stated square-zero law for the fixed polynomial
differential supplies this inclusion. -/
theorem boundaries_le_cycles (s t : ℕ) : boundaries s t ≤ cycles s t := by
  cases s with
  | zero => exact bot_le
  | succ s =>
      rintro x ⟨y, rfl⟩
      exact differential_squared s t y

end

/- Adapted from MilnorCohomology/Data.lean. -/
noncomputable section


/-- The actual incoming boundaries, included into the cycle module using the
square-zero theorem for this fixed polynomial differential. -/
def boundariesInCycles (s t : ℕ) : Submodule F2 (cycles s t) :=
  LinearMap.range (Submodule.inclusion (boundaries_le_cycles s t))

/-- Normalized cobar cohomology as an F₂-module quotient. -/
abbrev Cohomology (s t : ℕ) := (cycles s t) ⧸ boundariesInCycles s t

/-- The canonical linear map from actual cycles to their cohomology classes. -/
def classOf (s t : ℕ) : cycles s t →ₗ[F2] Cohomology s t :=
  (boundariesInCycles s t).mkQ

/-- The class of a specified closed normalized cochain. -/
def classOfCycle {s t : ℕ} (x : cochains s t) (hx : differential s t x = 0) :
    Cohomology s t :=
  classOf s t ⟨x, hx⟩

/-- Every quotient element has an actual normalized cocycle representative. -/
theorem classOfCycle_surjective {s t : ℕ} (z : Cohomology s t) :
    ∃ (x : cochains s t) (hx : differential s t x = 0), classOfCycle x hx = z := by
  obtain ⟨x, rfl⟩ := (boundariesInCycles s t).mkQ_surjective z
  exact ⟨x.val, x.property, rfl⟩

/-- The actual constant polynomial in the zero-fold tensor power. -/
def unitCochain : cochains 0 0 := by
  refine ⟨1, ?_, ?_⟩
  · exact MvPolynomial.isWeightedHomogeneous_one F2 weight
  · change (1 : TensorPower 0) ∈
      (⨅ slot : Fin 0, LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    exact Fin.elim0 slot

/-- The constant cochain is closed: the two coaugmentations cancel over F₂. -/
theorem unitCochain_isCycle : IsCycle unitCochain := by
  apply Subtype.ext
  change differentialPolynomial 0 1 = 0
  simp [differentialPolynomial, CharTwo.add_self_eq_zero]

/-- The cohomological unit is the class of the specified constant polynomial. -/
def unitClass : Cohomology 0 0 := classOfCycle unitCochain unitCochain_isCycle

/-- The class represented by `[ξ₁^(2^i)]`, not an independently chosen element. -/
def hiClass (i : ℕ) : Cohomology 1 (2 ^ i) :=
  classOfCycle (hiCochain i) (hiCochain_isCycle i)

/-- The class of the already defined concatenation square. Descent of the
full cup product to a cohomology ring is a separate construction. -/
def hiSquareClass (i : ℕ) : Cohomology 2 (2 ^ (i + 1)) :=
  classOfCycle (hiSquareCochain i) (hiSquareCochain_isCycle i)

end

/- Quotient criteria from MilnorCohomology/Proofs.lean. -/
noncomputable section


@[simp] theorem mem_boundariesInCycles {s t : ℕ} (x : cycles s t) :
    x ∈ boundariesInCycles s t ↔ x.val ∈ boundaries s t := by
  rw [boundariesInCycles, Submodule.range_inclusion]
  rfl

/-- The quotient kills precisely the incoming cobar boundaries. -/
theorem classOf_eq_zero_iff {s t : ℕ} (x : cycles s t) :
    classOf s t x = 0 ↔ x.val ∈ boundaries s t :=
  (Submodule.Quotient.mk_eq_zero _).trans (mem_boundariesInCycles x)

/-- Two specified cycles represent the same class exactly when their
actual cochains differ by an incoming cobar boundary. -/
theorem classOf_eq_iff {s t : ℕ} (x y : cycles s t) :
    classOf s t x = classOf s t y ↔
      x.val - y.val ∈ boundaries s t :=
  (Submodule.Quotient.eq _).trans (mem_boundariesInCycles (x - y))

theorem classOfCycle_eq_zero_iff {s t : ℕ} (x : cochains s t)
    (hx : differential s t x = 0) :
    classOfCycle x hx = 0 ↔ x ∈ boundaries s t :=
  classOf_eq_zero_iff ⟨x, hx⟩

/-- At zero there is no quotient by an artificial `d₋₁` or by `d₀`. -/
theorem classOfCycle_zero_eq_zero_iff (t : ℕ) (x : cochains 0 t)
    (hx : differential 0 t x = 0) :
    classOfCycle x hx = 0 ↔ x = 0 := by
  simpa only [boundaries_zero, Submodule.mem_bot] using classOfCycle_eq_zero_iff x hx

/-- In positive cohomological degree, zero means an actual preceding cochain
whose differential is the specified representative. -/
theorem classOfCycle_succ_eq_zero_iff (s t : ℕ) (x : cochains (s + 1) t)
    (hx : differential (s + 1) t x = 0) :
    classOfCycle x hx = 0 ↔ ∃ y : cochains s t, differential s t y = x :=
  classOfCycle_eq_zero_iff x hx

/-- Every differential represents zero; closedness is supplied by the
independent square-zero obligation for this same polynomial differential. -/
theorem classOf_differential (s t : ℕ) (x : cochains s t) :
    classOfCycle (differential s t x) (differential_squared s t x) = 0 :=
  (classOfCycle_succ_eq_zero_iff s t _ _).mpr ⟨x, rfl⟩

/-- Exact boundary criterion for the specified standard generator. -/
theorem hiClass_eq_zero_iff (i : ℕ) :
    hiClass i = 0 ↔
      ∃ b : cochains 0 (2 ^ i), differential 0 (2 ^ i) b = hiCochain i :=
  classOfCycle_succ_eq_zero_iff 0 (2 ^ i) _ _

/-- Exact boundary criterion for the specified concatenation square. -/
theorem hiSquareClass_eq_zero_iff (i : ℕ) :
    hiSquareClass i = 0 ↔ ∃ b : cochains 1 (2 ^ (i + 1)),
      differential 1 (2 ^ (i + 1)) b = hiSquareCochain i :=
  classOfCycle_succ_eq_zero_iff 1 (2 ^ (i + 1)) _ _

end

/- Adapted from MilnorCohomology/Multiplication/Cycles/Data.lean. -/
noncomputable section

/-- Concatenation of actual cycles, with closedness proved by Leibniz. -/
def cycleCup (s t s' t' : ℕ) :
    cycles s t →ₗ[F2] cycles s' t' →ₗ[F2] cycles (s + s') (t + t') where
  toFun x :=
    { toFun := fun y => ⟨cup x.val y.val, cup_isCycle _ _ x.property y.property⟩
      map_add' := fun y z => Subtype.ext (cup_add_right x.val y.val z.val)
      map_smul' := fun a y => Subtype.ext (cup_smul_right a x.val y.val) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact Subtype.ext (cup_add_left x.val y.val z.val)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (cup_smul_left a x.val y.val)


/-- The cohomology class of concatenation, before descending either input. -/
def cycleCupClass (s t s' t' : ℕ) :
    cycles s t →ₗ[F2] cycles s' t' →ₗ[F2] Cohomology (s + s') (t + t') :=
  (cycleCup s t s' t').compr₂ (classOf (s + s') (t + t'))

end

/- Adapted from MilnorCohomology/Multiplication/Cycles/Proofs.lean. -/
noncomputable section

theorem reindex_mem_boundaries_iff {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : cochains s t) : reindex hs ht x ∈ boundaries s' t' ↔ x ∈ boundaries s t := by
  subst s'
  subst t'
  rfl

theorem reindex_isCycle {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : cochains s t) (hx : IsCycle x) : IsCycle (reindex hs ht x) := by
  subst s'
  subst t'
  exact hx

/-- A boundary times a cycle is a boundary. At degree zero, the boundary
is zero; at positive degree its primitive is concatenated with the cycle. -/
theorem cup_boundary_cycle {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : x ∈ boundaries s t) (hy : IsCycle y) :
    cup x y ∈ boundaries (s + s') (t + t') := by
  cases s with
  | zero =>
      have hx0 : x = 0 := hx
      rw [hx0, cup_zero_left]
      exact Submodule.zero_mem _
  | succ s =>
      obtain ⟨b, rfl⟩ := hx
      have hd : differential (s + s') (t + t') (cup b y) =
          reindex (by omega) rfl (cup (differential s t b) y) := by
        rw [differential_cup, hy, cup_zero_right, map_zero, add_zero]
      apply (reindex_mem_boundaries_iff (by omega : (s + 1) + s' = (s + s') + 1)
        rfl _).mp
      exact ⟨cup b y, hd⟩

/-- A cycle times a boundary is a boundary, including the zero incoming
boundary module in degree zero. -/
theorem cup_cycle_boundary {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : y ∈ boundaries s' t') :
    cup x y ∈ boundaries (s + s') (t + t') := by
  cases s' with
  | zero =>
      have hy0 : y = 0 := hy
      rw [hy0, cup_zero_right]
      exact Submodule.zero_mem _
  | succ s' =>
      obtain ⟨b, rfl⟩ := hy
      have hd : differential (s + s') (t + t') (cup x b) =
          reindex (by omega) rfl (cup x (differential s' t' b)) := by
        rw [differential_cup, hx, cup_zero_left, map_zero, zero_add]
      apply (reindex_mem_boundaries_iff (by omega : s + (s' + 1) = (s + s') + 1)
        rfl _).mp
      exact ⟨cup x b, hd⟩


theorem boundaries_le_cycleCupClass_ker (s t s' t' : ℕ) :
    boundariesInCycles s t ≤ (cycleCupClass s t s' t').ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  apply (classOf_eq_zero_iff _).mpr
  exact cup_boundary_cycle x.val y.val ((mem_boundariesInCycles x).mp hx) y.property

theorem boundaries_le_cycleCupClass_flip_ker (s t s' t' : ℕ) :
    boundariesInCycles s' t' ≤ (cycleCupClass s t s' t').flip.ker := by
  intro y hy
  apply LinearMap.ext
  intro x
  apply (classOf_eq_zero_iff _).mpr
  exact cup_cycle_boundary x.val y.val x.property ((mem_boundariesInCycles y).mp hy)

end

/- Actual quotient descent from MilnorCohomology/Multiplication/Data.lean. -/
noncomputable section


/-- The bilinear cohomology product induced by the explicit cobar cup product.
Both quotient descents use proved Leibniz consequences. -/
def cohomologyCup {s t s' t' : ℕ} :
    Cohomology s t →ₗ[F2] Cohomology s' t' →ₗ[F2]
      Cohomology (s + s') (t + t') :=
  (cycleCupClass s t s' t').liftQ₂
    (boundariesInCycles s t) (boundariesInCycles s' t')
    (boundaries_le_cycleCupClass_ker s t s' t')
    (boundaries_le_cycleCupClass_flip_ker s t s' t')

/-- Transport along equalities of the two grading indices. -/
def cohomologyReindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t') :
    Cohomology s t ≃ₗ[F2] Cohomology s' t' := by
  subst s'
  subst t'
  exact LinearEquiv.refl F2 _

end

/- Representative formulas from MilnorCohomology/Multiplication/Proofs.lean. -/
noncomputable section

@[simp] theorem cohomologyCup_classOf {s t s' t' : ℕ} (x : cycles s t) (y : cycles s' t') :
    cohomologyCup (classOf s t x) (classOf s' t' y) =
      classOf (s + s') (t + t') (cycleCup s t s' t' x y) := rfl

/-- Multiplication of specified cocycle classes uses precisely their cobar
concatenation, with no independent choice of a representative. -/
theorem cohomologyCup_classOfCycle {s t s' t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : IsCycle y) :
    cohomologyCup (classOfCycle x hx) (classOfCycle y hy) =
      classOfCycle (KIP126.AdamsSynthetic.Milnor.cup x y) (cup_isCycle x y hx hy) := rfl

theorem cohomologyReindex_classOfCycle {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : cochains s t) (hx : IsCycle x) :
    cohomologyReindex hs ht (classOfCycle x hx) =
      classOfCycle (reindex hs ht x) (reindex_isCycle hs ht x hx) := by
  subst s'
  subst t'
  rfl

/-- Reindexing changes only the type index, not the represented class. -/
theorem cohomologyReindex_heq {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : Cohomology s t) : HEq (cohomologyReindex hs ht x) x := by
  subst s'
  subst t'
  rfl

/-- The specified hᵢ² class is the actual cup square, transported from
`2^i + 2^i` to its named internal degree `2^(i+1)`. -/
theorem hiSquare_eq_cup (i : ℕ) :
    hiSquareClass i =
      cohomologyReindex rfl (hiSquare_internalDegree i)
        (cohomologyCup (hiClass i) (hiClass i)) := by
  rw [hiClass, cohomologyCup_classOfCycle, cohomologyReindex_classOfCycle]
  rfl

end

end KIP126.AdamsSynthetic.Milnor
