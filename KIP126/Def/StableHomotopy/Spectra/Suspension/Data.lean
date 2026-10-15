module

public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

/-! Actual index shifts of sequential prespectra and their cubical
representatives. Desuspension pads the sequence with its based one-point
space; it does not apply a loop-space functor levelwise. -/

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

/-- The existing padded desuspension acts levelwise on maps. -/
def desuspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    desuspension X ⟶ desuspension Y where
  level
    | 0 => ContinuousMap.id _
    | n + 1 => f.level n
  point := by intro n; cases n with
    | zero => rfl
    | succ n => exact f.point n
  bond := by intro n x t; cases n with
    | zero => exact f.point 0
    | succ n => exact f.bond n x t

/-- Add the padded zero level without changing the actual cubical loop. -/
def Representative.pad {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X (d + 1)) : Representative (desuspension X) d where
  stage := a.stage + 1
  dimension := a.dimension
  degree := by have := a.degree; omega
  loop := a.loop

/-- Stabilize once before removing the padded zero level. This works even
for representatives initially placed in that zero level. -/
def Representative.unpadNext {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (desuspension X) d) : Representative X (d + 1) where
  stage := a.stage
  dimension := a.dimension + 1
  degree := by have := a.degree; omega
  loop := stabilizeLoop (desuspension X) a.stage a.dimension a.loop

/-- Remove the initial level from a sequential prespectrum. -/
def levelTail (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := X.level (n + 1)
  bond n := X.bond (n + 1)
  bond_point n := X.bond_point (n + 1)
  bond_zero n := X.bond_zero (n + 1)
  bond_one n := X.bond_one (n + 1)

/-- The padded tail maps to the original spectrum by the identity at every
positive level and the basepoint at level zero. -/
def paddedTailInclusion (X : Prespectrum.{u}) : desuspension (levelTail X) ⟶ X where
  level
    | 0 => ContinuousMap.const _ (X.level 0).point
    | n + 1 => ContinuousMap.id _
  point := by intro n; cases n <;> rfl
  bond := by intro n x t; cases n with
    | zero => exact (X.bond_point 0 t).symm
    | succ n => rfl

/-- After one stabilization a representative lies in the positive levels,
where the padded tail agrees with the original spectrum. -/
def Representative.liftPaddedTail {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) : Representative (desuspension (levelTail X)) d where
  stage := a.stage + 1
  dimension := a.dimension + 1
  degree := by have := a.degree; omega
  loop := stabilizeLoop X a.stage a.dimension a.loop

/-- Actual levelwise reduced suspension is functorial on strict prespectrum maps. -/
def suspensionFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj X := X.suspension
  map f := suspensionMap f
  map_id X := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,t⟩
    rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,t⟩
    rfl

end KIP126.StableHomotopy.Spectra.Prespectrum
