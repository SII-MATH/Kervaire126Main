module

public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monad.Algebra

@[expose] public section

/-!
The actual component maps of the right-tensor comonad attached to a comonoid
in an arbitrary monoidal category. This generic construction does not choose
a grading, a Steenrod coalgebra or a model of Ext. Its laws are stated in the
adjacent `Proofs` file before assembling the comonad.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory
open scoped ComonObj

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- A coaugmentation is an actual comonoid morphism from the canonical unit
comonoid. Its underlying arrow `η` satisfies `η ≫ ε = 𝟙` and
`η ≫ Δ = (λ_ (𝟙_ V)).inv ≫ (η ⊗ₘ η)`. -/
abbrev Coaugmentation (C : Comon V) := Comon.trivial V ⟶ C

namespace RightTensor

/-- The counit component for the actual functor `tensorRight C.X`. -/
def counitApp (C : Comon V) (X : V) : X ⊗ C.X ⟶ X :=
  (X ◁ ε[C.X]) ≫ (ρ_ X).hom

/-- The comultiplication component lands in `(X ⊗ C.X) ⊗ C.X`; the inverse
associator fixes the direction required for iterated right tensoring. -/
def comulApp (C : Comon V) (X : V) : X ⊗ C.X ⟶ (X ⊗ C.X) ⊗ C.X :=
  (X ◁ Δ[C.X]) ≫ (α_ X C.X C.X).inv

/-- Trivial coaction on the actual object `X`, induced by the specified
coaugmentation of the same comonoid. -/
def trivialCoaction {C : Comon V} (η : Coaugmentation C) (X : V) :
    X ⟶ X ⊗ C.X :=
  (ρ_ X).inv ≫ (X ◁ η.hom)

end RightTensor
end KIP126.Algebra.GradedComodule
