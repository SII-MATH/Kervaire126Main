module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

public import KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Data
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication

@[expose] section

/-! Concrete normalized Milnor cobar construction.
Adapted from SII-MATH/Kervaire126 (MIT), develop commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
These internal definitions have no chosen Adams page, named Ext class,
or computation data as input. -/

namespace KIP126.AdamsSynthetic.Milnor

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Data.lean. -/
noncomputable section


/-- The actual normalized cobar differential. -/
@[no_expose] public def differential (s t : ℕ) : cochains s t →ₗ[F2] cochains (s + 1) t :=
  ((differentialPolynomial s).comp (cochains s t).subtype).codRestrict _
    (differentialPolynomial_mem s t)

/-- The cochain product used to define the square. -/
def cup {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    cochains (s + s') (t + t') :=
  ⟨cupPolynomial x.val y.val, cupPolynomial_mem x y⟩

/-- The standard normalized cocycle representing `h₆`. -/
def h6Cochain : cochains 1 64 := ⟨h6Polynomial, h6Polynomial_mem⟩

/-- The square is the actual cochain concatenation product. -/
def h6SquareCochain : cochains 2 128 := cup h6Cochain h6Cochain

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Predicates.lean. -/
noncomputable section

set_option backward.privateInPublic true in
/-- A normalized cochain is a cocycle when its cobar differential is zero. -/
def IsCycle {s t : ℕ} (x : cochains s t) : Prop :=
  differential s t x = 0

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Proofs.lean. -/
noncomputable section

@[simp] theorem cup_add_left {s s' t t' : ℕ}
    (x x' : cochains s t) (y : cochains s' t') :
    cup (x + x') y = cup x y + cup x' y := by
  apply Subtype.ext
  simp [cup, cupPolynomial, add_mul]

@[simp] theorem cup_add_right {s s' t t' : ℕ}
    (x : cochains s t) (y y' : cochains s' t') :
    cup x (y + y') = cup x y + cup x y' := by
  apply Subtype.ext
  simp [cup, cupPolynomial, mul_add]

@[simp] theorem cup_smul_left {s s' t t' : ℕ}
    (a : F2) (x : cochains s t) (y : cochains s' t') :
    cup (a • x) y = a • cup x y := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

@[simp] theorem cup_smul_right {s s' t t' : ℕ}
    (a : F2) (x : cochains s t) (y : cochains s' t') :
    cup x (a • y) = a • cup x y := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

theorem h6Cochain_isCycle : IsCycle h6Cochain := by
  apply Subtype.ext
  exact h6Polynomial_differential

theorem h6SquareCochain_isCycle : IsCycle h6SquareCochain := by
  apply Subtype.ext
  exact h6SquarePolynomial_differential

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Reindex/Data.lean. -/
noncomputable section

/-- The canonical linear equivalence between equal cochain bidegrees. -/
def reindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t') :
    cochains s t ≃ₗ[F2] cochains s' t' := by
  subst s'
  subst t'
  exact LinearEquiv.refl _ _

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Reindex/Proofs.lean. -/
noncomputable section


@[simp] theorem reindex_rfl {s t : ℕ} (x : cochains s t) : reindex rfl rfl x = x := rfl

theorem reindex_val {s s' t t' : ℕ} (hs : s = s') (ht : t = t') (x : cochains s t) :
    (reindex hs ht x).val = Eq.mp (congrArg TensorPower hs) x.val := by
  subst s'
  subst t'
  rfl

theorem reindex_cup_val {s s' t t' n : ℕ} (h : s + s' = n)
    (x : cochains s t) (y : cochains s' t') :
    (reindex h rfl (cup x y)).val =
      blockRename (n := n) 0 (by omega) x.val * blockRename s (by omega) y.val := by
  subst n
  exact cupPolynomial_blocks x.val y.val

end

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Multiplication/Proofs.lean. -/
noncomputable section

/-- Concatenation satisfies the Leibniz identity over `𝔽₂`. -/
theorem differential_cup {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    differential (s + s') (t + t') (cup x y) =
      reindex (by omega) rfl (cup (differential s t x) y) +
      reindex (by omega) rfl (cup x (differential s' t' y)) := by
  apply Subtype.ext
  change differentialPolynomial (s + s') (cupPolynomial x.val y.val) =
    (reindex _ _ (cup (differential s t x) y)).val +
    (reindex _ _ (cup x (differential s' t' y))).val
  rw [reindex_cup_val, reindex_cup_val]
  exact differentialPolynomial_cup_blocks x.val y.val

@[simp] theorem cup_zero_left {s s' t t' : ℕ} (y : cochains s' t') :
    cup (0 : cochains s t) y = 0 := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

@[simp] theorem cup_zero_right {s s' t t' : ℕ} (x : cochains s t) :
    cup x (0 : cochains s' t') = 0 := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

/-- Products of cocycles are cocycles. -/
theorem cup_isCycle {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : IsCycle y) : IsCycle (cup x y) := by
  change differential _ _ (cup x y) = 0
  rw [differential_cup, hx, hy, cup_zero_left, cup_zero_right, map_zero, map_zero, zero_add]

end

end KIP126.AdamsSynthetic.Milnor
