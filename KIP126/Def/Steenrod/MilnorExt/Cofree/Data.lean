module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Realization.Data
public import KIP126.Def.Algebra.GradedComodule.Tensor.Data
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

/-!
The prescribed terms of the normalized cofree right-comodule resolution.
The polynomial realization concatenates the normalized word factors with
the final full coalgebra factor. The raw resolution differential has a
left coaugmentation and a coproduct in every slot, with no right insertion.
This component does not assert that the differential lifts to the terms,
that it squares to zero, or that the augmented sequence is an injective
resolution.
-/

namespace KIP126.Steenrod.Milnor.Ext.Cofree

noncomputable section
open CategoryTheory MonoidalCategory KIP126.Algebra
  KIP126.Algebra.GradedVectorSpace KIP126.Algebra.GradedComodule

/-- The actual normalized Milnor word coefficients, retaining integer
internal degrees. For length zero this includes the empty word. -/
def wordSpace (s : ℕ) : GrVect F2 :=
  fun n => ModuleCat.of F2 (MilnorWord s n →₀ F2)

/-- The specified cofree right-comodule term, on the same fixed Milnor
coalgebra. Its underlying graded space is `wordSpace s ⊗ dualSteenrod.X`. -/
def term (s : ℕ) : RightComodule Coalgebra.dualSteenrod :=
  (rightTensorComonad Coalgebra.dualSteenrod).cofree.obj (wordSpace s)

/-- The existing `cupPolynomial` as a bilinear map: the two actual slot
renamings followed by polynomial multiplication. -/
def cupBilinear (s s' : ℕ) :
    TensorPower s →ₗ[F2] TensorPower s' →ₗ[F2] TensorPower (s + s') :=
  (LinearMap.mul F2 (TensorPower (s + s'))).compl₁₂
    (MvPolynomial.rename
      (fun a : Fin s × ℕ => (a.1.castAdd s', a.2))).toLinearMap
    (MvPolynomial.rename
      (fun a : Fin s' × ℕ => (a.1.natAdd s, a.2))).toLinearMap

/-- Polynomial realization on one homogeneous Cauchy tensor summand. -/
def summandPolynomial (s : ℕ) (i j : ℤ) :
    (wordSpace s) i ⊗ Coalgebra.dualSteenrod.X j ⟶
      ModuleCat.of F2 (TensorPower (s + 1)) :=
  ModuleCat.ofHom (TensorProduct.lift
    ((cupBilinear s 1).compl₁₂ (milnorWordPolynomial s i) (Coalgebra.polynomial j)))

/-- Realize the actual cofree term by the Cauchy coproduct universal map,
using concatenation on every summand `i + j = n`. -/
def termPolynomial (s : ℕ) (n : ℤ) :
    (term s).A n →ₗ[F2] TensorPower (s + 1) :=
  (GradedObject.Monoidal.tensorObjDesc
    (X₁ := wordSpace s) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
    (fun i j _ => summandPolynomial s i j)).hom

/-- The cofree-resolution differential on the existing polynomial tensor
powers. The unrestricted final coalgebra slot contributes its coproduct;
there is no `insertRight` term in this resolution differential. -/
def rawDifferential (s : ℕ) :
    TensorPower (s + 1) →ₗ[F2] TensorPower (s + 2) :=
  (insertLeft (s + 1)).toLinearMap +
    ∑ slot : Fin (s + 1), (splitSlot slot).toLinearMap

end
end KIP126.Steenrod.Milnor.Ext.Cofree
