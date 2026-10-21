module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] section

/-! Concrete normalized Milnor cobar construction.
Adapted from SII-MATH/Kervaire126 (MIT), develop commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
These internal definitions have no chosen Adams page, named Ext class,
or computation data as input. -/

namespace KIP126.AdamsSynthetic.Milnor

/-- The coefficient field of this fixed cobar construction. -/
public abbrev F2 := ZMod 2

/- Adapted from KIP126/Def/Steenrod/MilnorCobar/Polynomial/Data.lean. -/
noncomputable section

open MvPolynomial
open scoped BigOperators

/-- The `s`fold tensor power of the polynomial dual Steenrod algebra.
The generator `(slot,j)` denotes `ξ_(j+1)` in that slot. -/
public abbrev TensorPower (s : ℕ) := MvPolynomial (Fin s × ℕ) F2

set_option backward.privateInPublic true in
/-- Milnor's grading, independent of the tensor slot. -/
def weight {s : ℕ} (a : Fin s × ℕ) : ℕ := 2 ^ (a.2 + 1) - 1

set_option backward.privateInPublic true in
/-- Include the convention `ξ₀ = 1` in the polynomial formula. -/
def xi {s : ℕ} (slot : Fin s) : ℕ → TensorPower s
  | 0 => 1
  | j + 1 => MvPolynomial.X (slot, j)

set_option backward.privateInPublic true in
/-- The Milnor coproduct, inserted at the specified adjacent tensor slots. -/
def coproductGenerator {s : ℕ} (slot : Fin s) (j : ℕ) : TensorPower (s + 1) :=
  ∑ i ∈ Finset.range (j + 2),
    xi slot.castSucc (j + 1 - i) ^ (2 ^ i) * xi slot.succ i

set_option backward.privateInPublic true in
/-- Apply the coproduct in one tensor slot. -/
def splitSlot {s : ℕ} (slot : Fin s) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.aeval fun a =>
    if a.1 = slot then coproductGenerator slot a.2
    else MvPolynomial.X (if a.1 < slot then a.1.castSucc else a.1.succ, a.2)

set_option backward.privateInPublic true in
/-- Insert the coaugmentation at the left end. -/
def insertLeft (s : ℕ) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.rename fun a => (a.1.succ, a.2)

set_option backward.privateInPublic true in
/-- Insert the coaugmentation at the right end. -/
def insertRight (s : ℕ) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.rename fun a => (a.1.castSucc, a.2)

set_option backward.privateInPublic true in
/-- Augment one slot by sending all its positive-degree generators to zero. -/
def augmentSlot {s : ℕ} (slot : Fin s) : TensorPower s →ₐ[F2] TensorPower s :=
  MvPolynomial.aeval fun a => if a.1 = slot then 0 else MvPolynomial.X a

/-- Homogeneous normalized cobar cochains. -/
@[no_expose] public def cochains (s t : ℕ) : Submodule F2 (TensorPower s) :=
  MvPolynomial.weightedHomogeneousSubmodule F2 weight t ⊓
    ⨅ slot : Fin s, LinearMap.ker (augmentSlot slot).toLinearMap

set_option backward.privateInPublic true in
/-- The characteristic-two cobar differential before restriction to normalized cochains. -/
def differentialPolynomial (s : ℕ) : TensorPower s →ₗ[F2] TensorPower (s + 1) :=
  (insertLeft s).toLinearMap + (insertRight s).toLinearMap +
    ∑ slot : Fin s, (splitSlot slot).toLinearMap

/-- Concatenation of tensor words, expressed by disjoint variable renamings. -/
def cupPolynomial {s s' : ℕ} (x : TensorPower s) (y : TensorPower s') :
    TensorPower (s + s') :=
  MvPolynomial.rename (fun a : Fin s × ℕ => (a.1.castAdd s', a.2)) x *
    MvPolynomial.rename (fun a : Fin s' × ℕ => (a.1.natAdd s, a.2)) y

/-- The polynomial representative `[ξ₁^64]`. -/
def h6Polynomial : TensorPower 1 := MvPolynomial.X (0, 0) ^ 64

end

end KIP126.AdamsSynthetic.Milnor
