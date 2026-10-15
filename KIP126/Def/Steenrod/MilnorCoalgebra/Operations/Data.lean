module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Raw.Proofs
public import KIP126.Def.Algebra.GradedVectorSpace.Data
public import Mathlib.CategoryTheory.Monoidal.Comon_

@[expose] public section

/-!
The actual Milnor graded comultiplication. Every supported monomial in
`splitSlot 0` contributes its coefficient to the Cauchy tensor summand
specified by the two slot degrees. Constants are retained in both factors.
-/

namespace KIP126.Steenrod.Milnor.Coalgebra

noncomputable section
open CategoryTheory MonoidalCategory KIP126.Algebra
  KIP126.Algebra.GradedVectorSpace
open scoped TensorProduct

/-- The full integer-graded dual Steenrod vector space. -/
def dualSteenrodGraded : GrVect F2 :=
  fun n => ModuleCat.of F2 (Carrier n)

/-- A single slot of a two-slot exponent vector, in its own actual degree. -/
def slotMonomial (d : (Fin 2 × ℕ) →₀ ℕ) (i : Fin 2) :
    MilnorMonomial (slotWeight (slotExponentsEquiv 2 d i) : ℤ) :=
  ⟨slotExponentsEquiv 2 d i, rfl⟩

/-- The actual coproduct of one full homogeneous basis monomial. -/
def comultiplicationMonomial {n : ℤ} (m : MilnorMonomial n) :
    (dualSteenrodGraded ⊗ dualSteenrodGraded) n :=
  (splitMonomial m).support.attach.sum fun d =>
    MvPolynomial.coeff d.val (splitMonomial m) •
      (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
        (slotWeight (slotExponentsEquiv 2 d.val 0) : ℤ)
        (slotWeight (slotExponentsEquiv 2 d.val 1) : ℤ) n
        (splitMonomial_support_degree m d.val d.property)).hom
        (Finsupp.single (slotMonomial d.val 0) 1 ⊗ₜ[F2]
          Finsupp.single (slotMonomial d.val 1) 1)

/-- Linear extension of the fixed basis coproduct, degree by degree. -/
def comultiplication :
    dualSteenrodGraded ⟶ dualSteenrodGraded ⊗ dualSteenrodGraded :=
  fun n => ModuleCat.ofHom (Finsupp.linearCombination F2
    (comultiplicationMonomial (n := n)))

/-- The actual constant coefficient, with zero components off degree zero. -/
def counit : dualSteenrodGraded ⟶ 𝟙_ (GrVect F2) := by
  classical
  intro n
  by_cases h : n = 0
  · subst n
    exact ModuleCat.ofHom (Finsupp.lapply zeroMilnorMonomial) ≫
      GradedObject.Monoidal.tensorUnit₀.inv
  · exact 0

/-- The actual constant polynomial as a graded map from the tensor unit. -/
def coaugmentationMap : 𝟙_ (GrVect F2) ⟶ dualSteenrodGraded := by
  classical
  intro n
  by_cases h : n = 0
  · subst n
    exact GradedObject.Monoidal.tensorUnit₀.hom ≫
      ModuleCat.ofHom (Finsupp.lsingle zeroMilnorMonomial)
  · exact 0

end
end KIP126.Steenrod.Milnor.Coalgebra
