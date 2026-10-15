module

public import KIP126.Def.Algebra.GradedComodule.Tensor.Raw.Proofs

@[expose] public section

/-!
The right-tensor comonad and its actual category of right comodules. The
underlying functor, natural transformations and coactions use precisely the
comonoid's counit and comultiplication with the given monoidal coherence.
No alternative comonad or arbitrary category of comodules is selected.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

namespace RightTensor

/-- Counit natural transformation of the actual right-tensor functor. -/
def counit (C : Comon V) : tensorRight C.X ⟶ 𝟭 V where
  app := counitApp C
  naturality _ _ f := counit_naturality C f

/-- Comultiplication natural transformation of the same right-tensor functor. -/
def comul (C : Comon V) : tensorRight C.X ⟶ tensorRight C.X ⋙ tensorRight C.X where
  app := comulApp C
  naturality _ _ f := comul_naturality C f

end RightTensor

/-- The comonad `X ↦ X ⊗ C.X`, with counit `(X ◁ ε) ≫ ρ_X` and
comultiplication `(X ◁ Δ) ≫ α⁻¹`. -/
def rightTensorComonad (C : Comon V) : Comonad V where
  toFunctor := tensorRight C.X
  ε := RightTensor.counit C
  δ := RightTensor.comul C
  coassoc := RightTensor.coassoc C
  left_counit := RightTensor.left_counit C
  right_counit := RightTensor.right_counit C

/-- Actual right comodules, including their coaction axioms and the ordinary
category of coaction-preserving morphisms, are Eilenberg–Moore coalgebras for
the specified right-tensor comonad. -/
abbrev RightComodule (C : Comon V) := Comonad.Coalgebra (rightTensorComonad C)

/-- Forget exactly the coaction, retaining the same underlying object and map. -/
def forget (C : Comon V) : RightComodule C ⥤ V :=
  Comonad.forget (rightTensorComonad C)

/-- Trivial right comodule on any object, using the specified coaugmentation.
Its coaction is definitionally `(ρ_ X).inv ≫ (X ◁ η.hom)`. -/
def trivialComodule {C : Comon V} (η : Coaugmentation C) (X : V) : RightComodule C where
  A := X
  a := RightTensor.trivialCoaction η X
  counit := RightTensor.trivial_counit η X
  coassoc := RightTensor.trivial_coassoc η X

/-- The trivial comodule construction keeps each ordinary map unchanged. -/
def trivialComoduleFunctor {C : Comon V} (η : Coaugmentation C) : V ⥤ RightComodule C where
  obj := trivialComodule η
  map f := ⟨f, RightTensor.trivial_naturality η f⟩

end KIP126.Algebra.GradedComodule
