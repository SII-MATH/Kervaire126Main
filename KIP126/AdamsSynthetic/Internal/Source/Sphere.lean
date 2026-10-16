module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Prespectrum

@[expose] section

/-!
# The concrete sphere and shifts in the sequential-prespectrum source

The zero sphere is the discrete based two-point space. Higher sphere levels
are the actual reduced suspension quotients, with bonding maps the quotient
projections. Suspension and desuspension are explicit operations on the same
prespectra; they are not unspecified object choices.

Adapted from `Implementation/PointSet.lean` and the padding desuspension in
`Implementation/Generators.lean`, SII-MATH/Kervaire126 develop commit
`8cb35dad5f75ecc095e474df6c765baec9b175bf`.
-/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace BasedSpace

/-- The actual basepoint inclusion is closed and has the homotopy extension
property against continuous maps, the hypothesis needed for reduced suspension. -/
def IsWellBased (X : BasedSpace.{u}) : Prop :=
  IsClosed ({X.point} : Set X) ∧
    ∀ (Y : TopCat.{u}) (f : C(X,Y)) (p : C(I,Y)), p 0 = f X.point →
      ∃ H : C(X × I,Y), (∀ x, H (x,0) = f x) ∧ (∀ t, H (X.point,t) = p t)

def SuspensionCollapsed (X : BasedSpace.{u}) (p : X × I) : Prop :=
  p.1 = X.point ∨ p.2 = 0 ∨ p.2 = 1

def SuspensionRelation (X : BasedSpace.{u}) (p q : X × I) : Prop :=
  SuspensionCollapsed X p ∧ SuspensionCollapsed X q

def suspension (X : BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of (Quot (SuspensionRelation X))
  point := Quot.mk _ (X.point, 0)

def suspensionProjection (X : BasedSpace.{u}) : C(X × I, X.suspension) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

theorem suspensionProjection_collapsed (X : BasedSpace.{u}) (p : X × I)
    (h : SuspensionCollapsed X p) : suspensionProjection X p = X.suspension.point :=
  Quot.sound ⟨h, Or.inl rfl⟩

/-- Pointwise suspension of a based continuous family of maps. -/
def suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) (p : X.suspension × I) : Y.suspension :=
  Quot.lift (fun q : X × I => suspensionProjection Y (f (q.1,p.2),q.2))
    (by
      intro a b hab
      apply Eq.trans _ (suspensionProjection_collapsed Y _ ?_).symm
      · apply suspensionProjection_collapsed
        rcases hab.1 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases hab.2 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) p.1

theorem continuous_suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) : Continuous (suspensionFamily X Y f hf) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  exact (suspensionProjection Y).continuous.comp
    ((f.continuous.comp ((continuous_fst.fst).prodMk continuous_snd)).prodMk
      continuous_fst.snd)

def suspensionMap (X Y : BasedSpace.{u}) (f : C(X,Y)) (hf : f X.point = Y.point) :
    C(X.suspension,Y.suspension) := by
  let raw : C(X × I,Y.suspension) :=
    (suspensionProjection Y).comp ⟨fun p => (f p.1,p.2),
      (f.continuous.comp continuous_fst).prodMk continuous_snd⟩
  have respects : ∀ a b, SuspensionRelation X a b → raw a = raw b := by
    intro a b hab
    have collapsed : ∀ p, SuspensionCollapsed X p → raw p = Y.suspension.point := by
      intro p hp
      apply suspensionProjection_collapsed
      rcases hp with h | h | h
      · left
        change f p.1 = Y.point
        rw [h]
        exact hf
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact (collapsed a hab.1).trans (collapsed b hab.2).symm
  exact ⟨Quot.lift raw respects, continuous_quot_lift respects raw.continuous⟩

end BasedSpace

namespace Prespectrum

def IsWellBased (X : Prespectrum.{u}) : Prop := ∀ n, (X.level n).IsWellBased

/-- The sphere prespectrum has level Sⁿ, formed by iterated actual reduced
suspension of the discrete based two-point space. -/
def sphereLevel : ℕ → BasedSpace
  | 0 => { space := TopCat.of (Fin 2), point := 0 }
  | n + 1 => (sphereLevel n).suspension

def sphere : Prespectrum where
  level := sphereLevel
  bond n := BasedSpace.suspensionProjection (sphereLevel n)
  bond_point _n _t := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

/-- The positive generator of π₀ of the ordinary sphere: the non-basepoint
of S⁰, viewed as a zero-dimensional cubical loop. -/
def sphereGenerator : StableHomotopy sphere 0 :=
  loopClass sphere 0 0 0 (by norm_num)
    ⟨ContinuousMap.const _ (show sphere.level 0 from (1 : Fin 2)), by
      intro t ht
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i⟩

/-- Levelwise reduced suspension with the displayed interchange of the two
interval variables. This is not an independently selected shift operation. -/
def suspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := (X.level n).suspension
  bond n := ⟨BasedSpace.suspensionFamily _ _ (X.bond n) (X.bond_point n),
    BasedSpace.continuous_suspensionFamily _ _ (X.bond n) (X.bond_point n)⟩
  bond_point := by
    intro n t
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_zero := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,0),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_zero n _))
  bond_one := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,1),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_one n _))

def suspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  level n := BasedSpace.suspensionMap _ _ (f.level n) (f.point n)
  point := by
    intro n
    change BasedSpace.suspensionProjection _ (f.level n (X.level n).point,0) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond := by
    intro n x t
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (f.level (n+1) (X.bond n (p.1,t)),p.2) =
      BasedSpace.suspensionProjection _ (Y.bond n (f.level n p.1,t),p.2)
    rw [f.bond]

/-- Padding with one zero level gives an actual desuspension prespectrum. -/
def desuspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level
    | 0 => { space := TopCat.of PUnit, point := PUnit.unit }
    | n+1 => X.level n
  bond
    | 0 => ContinuousMap.const _ (X.level 0).point
    | n+1 => X.bond n
  bond_point := by intro n t; cases n <;> simp [X.bond_point]
  bond_zero := by intro n x; cases n <;> simp [X.bond_zero]
  bond_one := by intro n x; cases n <;> simp [X.bond_one]

/-- The actual map on the padding desuspensions, with the unique zero-level map. -/
def desuspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X.desuspension ⟶ Y.desuspension where
  level
    | 0 => ContinuousMap.id _
    | n + 1 => f.level n
  point := by
    intro n
    cases n with
    | zero => rfl
    | succ n => exact f.point n
  bond := by
    intro n x t
    cases n with
    | zero => exact f.point 0
    | succ n => exact f.bond n x t

end Prespectrum

end KIP126.AdamsSynthetic.Source
