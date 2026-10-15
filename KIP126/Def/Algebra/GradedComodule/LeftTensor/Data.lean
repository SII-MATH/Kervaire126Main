module

public import KIP126.Def.Algebra.GradedComodule.Tensor.Data

@[expose] public section

/-!
The left action of the ambient monoidal category on right comodules.
The coaction tensors the existing coaction and uses the existing associator;
it does not choose a new comodule structure. This also supplies the underlying
construction for internal shifts of graded comodules.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The actual coaction on `X ⊗ A`, with `A` a right `C`-comodule. -/
def leftTensorCoaction (C : Comon V) (X : V) (A : RightComodule C) :
    X ⊗ A.A ⟶ (X ⊗ A.A) ⊗ C.X :=
  X ◁ A.a ≫ (α_ X A.A C.X).inv

end KIP126.Algebra.GradedComodule
