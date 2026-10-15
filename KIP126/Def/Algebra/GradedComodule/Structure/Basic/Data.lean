module

public import KIP126.Def.Algebra.GradedComodule.Tensor.Data
public import KIP126.Def.Algebra.GradedVectorSpace.Proofs
public import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
public import Mathlib.CategoryTheory.Monad.Limits

@[expose] public section

/-!
Linear operations and finite limits/colimits for the actual category of
graded right comodules. Addition is Mathlib's existing coalgebra addition.
Scalar multiplication is the ordinary scalar multiplication on the same
underlying morphisms. Limits and colimits use the actual Eilenberg--Moore
creation constructions; no kernel or cokernel object is supplied by `sorry`.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open GradedVectorSpace

universe u

noncomputable section

variable {K : Type u} [Field K] (C : Comon (GrVect K))

instance rightTensorComonad_additive :
    Functor.Additive (rightTensorComonad C : GrVect K ⥤ GrVect K) :=
  GradedVectorSpace.tensorRight_additive C.X

instance rightTensorComonad_linear :
    Functor.Linear K (rightTensorComonad C : GrVect K ⥤ GrVect K) :=
  GradedVectorSpace.tensorRight_linear C.X

instance rightTensorComonad_preservesFiniteLimits :
    PreservesFiniteLimits (rightTensorComonad C : GrVect K ⥤ GrVect K) :=
  GradedVectorSpace.tensorRight_preservesFiniteLimits C.X

instance homSMul (X Y : RightComodule C) : SMul K (X ⟶ Y) where
  smul r f :=
    { f := r • f.f
      h := by
        calc
          X.a ≫ (rightTensorComonad C).map (r • f.f) =
              X.a ≫ (r • (rightTensorComonad C).map f.f) :=
            congrArg (X.a ≫ ·) (Functor.map_smul _ _ _)
          _ = r • (X.a ≫ (rightTensorComonad C).map f.f) :=
            Linear.comp_smul _ _ _ _ _ _
          _ = r • (f.f ≫ Y.a) := congrArg (r • ·) f.h
          _ = (r • f.f) ≫ Y.a := (Linear.smul_comp _ _ _ _ _ _).symm }

/-- Forgetting the coaction is an injective additive map on morphisms, with
the existing Eilenberg--Moore additive structure. -/
def homForgetAddHom (X Y : RightComodule C) : (X ⟶ Y) →+ (X.A ⟶ Y.A) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

instance homModule (X Y : RightComodule C) : Module K (X ⟶ Y) :=
  Function.Injective.module K (homForgetAddHom C X Y)
    (fun _ _ h => Comonad.Coalgebra.Hom.ext h) (fun _ _ => rfl)

instance linear : Linear K (RightComodule C) where
  homModule := homModule C
  smul_comp _ _ _ r f g := by
    apply Comonad.Coalgebra.Hom.ext
    change (r • f.f) ≫ g.f = r • (f.f ≫ g.f)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ f r g := by
    apply Comonad.Coalgebra.Hom.ext
    change f.f ≫ (r • g.f) = r • (f.f ≫ g.f)
    exact Linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear K (forget C) where
  map_smul _ _ := rfl

instance hasFiniteLimits : HasFiniteLimits (RightComodule C) where
  out _ :=
    { has_limit F := Comonad.forget_creates_limits_of_comonad_preserves F }

instance hasFiniteColimits : HasFiniteColimits (RightComodule C) where
  out _ :=
    { has_colimit F := Comonad.hasColimit_of_comp_forget_hasColimit F }

end
end KIP126.Algebra.GradedComodule
