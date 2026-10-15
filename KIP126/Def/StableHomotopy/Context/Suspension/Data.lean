module

public import KIP126.Def.StableHomotopy.Context.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Desuspend a represented homotopy class using the given shift coherence.
This operation does not involve any triangle or Adams construction. -/
noncomputable def homotopyDesuspend (X : C) (n : ℤ) :
    HomotopyGroup n (X⟦(1 : ℤ)⟧) →+ HomotopyGroup (n - 1) X where
  toFun z := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map z ≫ (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app X
  map_zero' := by simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' x y := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end KIP126.StableHomotopy
