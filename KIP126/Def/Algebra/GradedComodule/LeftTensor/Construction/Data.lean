module

public import KIP126.Def.Algebra.GradedComodule.LeftTensor.Proofs

@[expose] public section

/-! The actual left tensor action on the category of right comodules. -/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- Left tensoring a right comodule by an ambient object. -/
def leftTensorObject (C : Comon V) (X : V) (A : RightComodule C) :
    RightComodule C where
  A := X ⊗ A.A
  a := leftTensorCoaction C X A
  counit := leftTensorCoaction_counit C X A
  coassoc := leftTensorCoaction_coassoc C X A

/-- On morphisms the left tensor action is the existing whiskering. -/
def leftTensorFunctor (C : Comon V) (X : V) : RightComodule C ⥤ RightComodule C where
  obj A := leftTensorObject C X A
  map f := ⟨X ◁ f.f, leftTensorCoaction_map C X f⟩
  map_id A := Comonad.Coalgebra.Hom.ext ((tensorLeft X).map_id A.A)
  map_comp f g := Comonad.Coalgebra.Hom.ext ((tensorLeft X).map_comp f.f g.f)

end KIP126.Algebra.GradedComodule
