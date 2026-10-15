module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Linear.FunctorCategory

@[expose] public section

/-!
Integer-graded vector spaces with the Cauchy tensor product. The tensor in
degree `n` is the coproduct of `X i ⊗ Y j` over `i + j = n`, using Mathlib's
graded-object monoidal structure, not a pointwise tensor. The additive and
linear structures are pointwise on morphisms. The abelian structure is
transported along the actual equivalence with functors from the discrete
category of integers; no abelian-category witness is an extra input.
-/

namespace KIP126.Algebra.GradedVectorSpace

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

/-- Integer-graded vector spaces over `K`, in the same universe as `K`. -/
abbrev GrVect (K : Type u) [Field K] :=
  GradedObject ℤ (ModuleCat.{u} K)

variable (K : Type u) [Field K]

instance : Preadditive (GrVect K) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((n : ℤ) → (X n ⟶ Y n)))
  add_comp _ _ _ f g h := by
    funext n
    exact Preadditive.add_comp _ _ _ (f n) (g n) (h n)
  comp_add _ _ _ f g h := by
    funext n
    exact Preadditive.comp_add _ _ _ (f n) (g n) (h n)

instance : Linear K (GrVect K) where
  homModule X Y := inferInstanceAs (Module K ((n : ℤ) → (X n ⟶ Y n)))
  smul_comp _ _ _ r f g := by
    funext n
    exact Linear.smul_comp (r := r) (f := f n) (g := g n)
  comp_smul _ _ _ f r g := by
    funext n
    exact Linear.comp_smul (f := f n) (r := r) (g := g n)

/-- The actual pointwise equivalence, used to transport finite limits and
the abelian structure without replacing the Cauchy tensor product. -/
def discreteEquivalence : GrVect K ≌ (Discrete ℤ ⥤ ModuleCat.{u} K) :=
  piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} K)

instance : HasFiniteLimits (GrVect K) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (discreteEquivalence K).functor⟩

noncomputable instance : Abelian (GrVect K) :=
  abelianOfEquivalence (discreteEquivalence K).functor

/-- The Cauchy inclusion of the indicated homogeneous tensor summand. -/
noncomputable def tensorInclusion (X Y : GrVect K) (i j n : ℤ) (h : i + j = n) :
    X i ⊗ Y j ⟶ (X ⊗ Y) n :=
  GradedObject.Monoidal.ιTensorObj X Y i j n h

end KIP126.Algebra.GradedVectorSpace
