module

/-
Copyright (c) 2026 KIP126 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KIP126 contributors
-/
public import KIP126.SpectralSequence.Permanence.Predicates
public import KIP126.SpectralSequence.Convergence.Category.Data
public import Mathlib.Data.ZMod.Basic

@[expose] section

/-! Multiplicative contracts for the given module-valued spectral sequences.
The bilinear formulation works in every module universe, including integer
modules whose objects live in a larger universe than ℤ. Successor products
preserve the actual common representative relation. The same Z∞ product
binds every finite page to E∞ and to the actual filtered abutment.
Source: KIPBase `multiplicativeSS/Basic.lean`, baseline 5aa845241533. -/
namespace KIP126.Core.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [CommRing R]
noncomputable section

public abbrev GradingParity := (ℤ × ℤ) →+ ZMod 2

/-- The actual infinite cycles in the nested-subobject model. -/
public abbrev InfiniteCycles (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) :=
  (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat R)

/-- Restrict one infinite cycle to a displayed finite page. -/
public def infinityToPage (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) : InfiniteCycles E p ⟶ E.Page r p :=
  Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top) ≫
    (E.ssData p).pageπ ↑(r - E.r₀).toNat

/-- Transport only along an equality of grading indices. -/
public def transportPage (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) {p q : ℤ × ℤ} (h : p = q) : E.Page r p ⟶ E.Page r q :=
  eqToHom (congrArg (E.Page r) h)

/-- A bilinear product on every page, with signed differential law and
 descent along the actual next-page relation. The latter replaces independent
 choices of products on homology and the following page. -/
public structure SSPairing (E₁ E₂ E₃ : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) where
  diffDeg_compatible : ∀ r : ℤ,
    E₁.diffDeg r = E₂.diffDeg r ∧ E₁.diffDeg r = E₃.diffDeg r
  parity : GradingParity
  pair : ∀ (r : ℤ) (k l : ℤ × ℤ),
    E₁.Page r k →ₗ[R] E₂.Page r l →ₗ[R] E₃.Page r (k + l)
  leibniz : ∀ (r : ℤ) (k l : ℤ × ℤ) (x : E₁.Page r k) (y : E₂.Page r l),
    E₃.d r (k + l) (pair r k l x y) =
      (transportPage E₃ r (by rw [(diffDeg_compatible r).2]; ac_rfl))
        (pair r (k + E₁.diffDeg r) l (E₁.d r k x) y) +
      (if parity k = 1 then (-1 : ℤ) else 1) •
        (transportPage E₃ r (by rw [← (diffDeg_compatible r).1, (diffDeg_compatible r).2]; ac_rfl))
          (pair r k (l + E₂.diffDeg r) x (E₂.d r l y))
  nextPage_compatible : ∀ (r : ℤ) (k l : ℤ × ℤ),
    E₁.r₀ ≤ r → E₂.r₀ ≤ r → E₃.r₀ ≤ r →
    ∀ (x : E₁.Page r k) (x' : E₁.Page (r + 1) k)
      (y : E₂.Page r l) (y' : E₂.Page (r + 1) l),
    NextPageRelation E₁ r k x x' → NextPageRelation E₂ r l y y' →
    NextPageRelation E₃ r (k + l) (pair r k l x y) (pair (r + 1) k l x' y')

/-- The actual submodule object at one filtration level. -/
public abbrev FiltrationPiece {A : ℤ → ModuleCat.{v} R} (F : Filtration A) (s n : ℤ) :=
  (Subobject.underlying.obj (F.F s n) : ModuleCat R)

/-- Full multiplication data on one converging triple. All the intermediate
products are constrained by quotient and inclusion equations, so they cannot
silently be chosen independently. -/
public structure ConvergingSSPairing
    (X₁ X₂ X₃ : ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ) where
  ssPairing : SSPairing X₁.E X₂.E X₃.E
  eInftyPair : ∀ k l : ℤ × ℤ,
    (X₁.E.ssData k).eInfty →ₗ[R] (X₂.E.ssData l).eInfty →ₗ[R]
      (X₃.E.ssData (k + l)).eInfty
  cyclePairAtInfinity : ∀ k l : ℤ × ℤ,
    InfiniteCycles X₁.E k →ₗ[R] InfiniteCycles X₂.E l →ₗ[R] InfiniteCycles X₃.E (k + l)
  eInftyPair_induced : ∀ (k l : ℤ × ℤ)
      (x : InfiniteCycles X₁.E k) (y : InfiniteCycles X₂.E l),
    (X₃.E.ssData (k + l)).pageπ ⊤ (cyclePairAtInfinity k l x y) =
      eInftyPair k l ((X₁.E.ssData k).pageπ ⊤ x) ((X₂.E.ssData l).pageπ ⊤ y)
  finitePagePair_compatible : ∀ (r : ℤ) (k l : ℤ × ℤ),
    X₁.E.r₀ ≤ r → X₂.E.r₀ ≤ r → X₃.E.r₀ ≤ r →
    ∀ (x : InfiniteCycles X₁.E k) (y : InfiniteCycles X₂.E l),
    ssPairing.pair r k l (infinityToPage X₁.E r k x) (infinityToPage X₂.E r l y) =
      infinityToPage X₃.E r (k + l) (cyclePairAtInfinity k l x y)
  abutmentPair : ∀ i j : ℤ, X₁.A i →ₗ[R] X₂.A j →ₗ[R] X₃.A (i + j)
  filteredAbutmentPair : ∀ s t i j : ℤ,
    FiltrationPiece X₁.F s i →ₗ[R] FiltrationPiece X₂.F t j →ₗ[R]
      FiltrationPiece X₃.F (s + t) (i + j)
  filteredAbutmentPair_compatible : ∀ (s t i j : ℤ)
      (x : FiltrationPiece X₁.F s i) (y : FiltrationPiece X₂.F t j),
    (X₃.F.F (s + t) (i + j)).arrow (filteredAbutmentPair s t i j x y) =
      abutmentPair i j ((X₁.F.F s i).arrow x) ((X₂.F.F t j).arrow y)
  associatedGradedPair : ∀ s t i j : ℤ,
    X₁.F.associatedGraded s i →ₗ[R] X₂.F.associatedGraded t j →ₗ[R]
      X₃.F.associatedGraded (s + t) (i + j)
  associatedGradedPair_induced : ∀ (s t i j : ℤ)
      (x : FiltrationPiece X₁.F s i) (y : FiltrationPiece X₂.F t j),
    associatedGradedPair s t i j (X₁.F.toAssociatedGraded s i x)
        (X₂.F.toAssociatedGraded t j y) =
      X₃.F.toAssociatedGraded (s + t) (i + j) (filteredAbutmentPair s t i j x y)
  reindex_compatible : ∀ k l : ℤ × ℤ,
    X₁.conv.reindex k + X₂.conv.reindex l = X₃.conv.reindex (k + l)
  eInfty_compatible : ∀ (k l : ℤ × ℤ)
      (x : (X₁.E.ssData k).eInfty) (y : (X₂.E.ssData l).eInfty),
    X₃.F.transportGraded (reindex_compatible k l).symm
      ((X₃.conv.iso (k + l)).hom (eInftyPair k l x y)) =
      associatedGradedPair (X₁.conv.reindex k).1 (X₂.conv.reindex l).1
        (X₁.conv.reindex k).2 (X₂.conv.reindex l).2
        ((X₁.conv.iso k).hom x) ((X₂.conv.iso l).hom y)

/-- Unit data tied to one common infinite cycle and a representative in
filtration zero of the actual abutment. -/
public structure ConvergingSSUnit (X : ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ)
    (hzero : X.conv.reindex (0, 0) = (0, 0)) where
  cycle : InfiniteCycles X.E (0, 0)
  filtered : FiltrationPiece X.F 0 0
  compatible : X.F.transportGraded hzero
      ((X.conv.iso (0, 0)).hom ((X.E.ssData (0, 0)).pageπ ⊤ cycle)) =
    X.F.toAssociatedGraded 0 0 filtered

namespace ConvergingSSUnit
variable {X : ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ}
  {hzero : X.conv.reindex (0, 0) = (0, 0)}
public def page (U : ConvergingSSUnit X hzero) (r : ℤ) : X.E.Page r (0, 0) :=
  infinityToPage X.E r (0, 0) U.cycle
public def eInfty (U : ConvergingSSUnit X hzero) : (X.E.ssData (0, 0)).eInfty :=
  (X.E.ssData (0, 0)).pageπ ⊤ U.cycle
public def abutment (U : ConvergingSSUnit X hzero) : X.A 0 :=
  (X.F.F 0 0).arrow U.filtered
end ConvergingSSUnit
end
end KIP126.Core.SpectralSequence
