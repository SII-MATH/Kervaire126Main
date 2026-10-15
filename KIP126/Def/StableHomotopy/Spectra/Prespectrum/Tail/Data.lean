module

public import KIP126.Def.StableHomotopy.Spectra.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

def desuspensionStableHomotopyLift (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X (d+1) → StableHomotopy (desuspension X) d :=
  Quot.map Representative.pad (by
    intro a b hab
    cases hab with
    | homotopy p hp => exact StableRelation.homotopy a.pad _ hp
    | stabilization => exact StableRelation.stabilization a.pad)

def evaluationFunctor (n : ℕ) : Prespectrum.{u} ⥤ BasedSpace.{u} where
  obj X := X.level n
  map f := ⟨f.level n,f.point n⟩

def desuspensionFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj X := desuspension X
  map f := desuspensionMap f
  map_id X := by
    apply Hom.ext
    funext n
    cases n <;> rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    cases n <;> rfl

def levelTailMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : levelTail X ⟶ levelTail Y where
  level n := f.level (n+1)
  point n := f.point (n+1)
  bond n := f.bond (n+1)

def levelTailFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj X := levelTail X
  map f := levelTailMap f

end KIP126.StableHomotopy.Spectra.Prespectrum
