module

public import KIP126.Def.Algebra.GradedVectorSpace.Data
public import KIP126.Def.Algebra.GradedComodule.LeftTensor.Construction.Data
public import Mathlib.CategoryTheory.GradedObject.Single

@[expose] public section

/-!
Internal grading and cohomological grading are distinct. The object `degreeLine K t`
is the one-dimensional vector space in internal degree `t`. Tensoring it on the
left shifts a right comodule so that its old degree `n - t` contributes to degree
`n`. This uses the Cauchy tensor of graded vector spaces, not the pointwise tensor.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

noncomputable section

/-- The one-dimensional graded vector space concentrated in degree `t`. -/
def degreeLine (t : ℤ) : GrVect K :=
  (GradedObject.single t).obj (ModuleCat.of K K)

/-- The actual element `1` in the unique nonzero component of `degreeLine`. -/
def degreeLineGenerator (t : ℤ) : degreeLine K t t :=
  (GradedObject.singleObjApplyIso t (ModuleCat.of K K)).inv.hom 1

/-- Internal suspension uses the actual Cauchy left tensor functor. -/
def internalShift (C : Comon (GrVect K)) (t : ℤ) :
    RightComodule C ⥤ RightComodule C :=
  leftTensorFunctor C (degreeLine K t)

/-- The trivial right comodule concentrated in exactly internal degree `t`.
Its coaction uses the specified coaugmentation of the same coalgebra. -/
def trivialAt {C : Comon (GrVect K)} (η : Coaugmentation C) (t : ℤ) :
    RightComodule C :=
  trivialComodule η (degreeLine K t)

end

end KIP126.Algebra.GradedComodule
